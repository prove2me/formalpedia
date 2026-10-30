-- Prove2me | Theorems.Thm_FuzzyExtractors_ImprovedJSFull_theorem_6_1_full
-- name    : FuzzyExtractors.ImprovedJSFull.theorem_6_1_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:36:00.46508+00:00
-- url     : https://prove2.me/theorems/030c1ab8-bcd1-41dd-8ed9-53513f28f5bc
-- title:
--   Theorem 6.1 — full improved Juels–Sudan sketch: entropy, storage and expected polynomial time
-- statement:
--   Let $F$ be any finite field of size $n$, and let $0\le t\le s\le n$. Let Construction 5's deterministic sketch return the top $t$ nonleading coefficients of $\prod_{x\in w}(z-x)$ for each $s$-element set $w$. Recovery uses the stated Reed–Solomon agreement condition and the roots of the high polynomial minus the decoded low polynomial.
--
--   There exist two finite binary-tape programs, a real constant $C>0$ and a natural exponent $d$, all uniform over the finite fields, presentations, parameters and input sets, with the following properties. Every finite field admits the specified polynomial-basis presentation. Every such presentation has injectively encoded field elements and a descriptor of polynomial size in $\log_2 n$. The sketch program is syntactically deterministic and outputs exactly the coefficient vector. The recovery program realizes the decoder-and-roots relation and refines the published semantic recovery. On all well-formed inputs, including arbitrary mismatched $t$-symbol sketches, both programs terminate almost surely and satisfy
--
--   $$\mathbb E[T_{\mathsf{SS}}],\ \mathbb E[T_{\mathsf{Rec}}]\le C(1+s+t+\lceil\log_2 n\rceil)^d.$$
--
--   Every helper consists of exactly $t$ field symbols, its carrier has $n^t$ possibilities, and
--
--   $$\log_2|F^t|\le t\log_2 n.$$
--
--   A packed injective binary representation exists of length $\lceil t\log_2 n\rceil$; the operational digitwise encoding has length $tk\lceil\log_2 p\rceil$ when $n=p^k$.
--
--   For every real $m$, the semantic procedures, realized by these programs, form an average-case $(\mathrm{SDif}_s(F),m,m-t\log_2 n,t)$ secure sketch. Correctness has probability one for every pair at symmetric-difference distance at most $t$. For every jointly distributed secret and arbitrary auxiliary information,
--
--   $$\widetilde H_\infty(W\mid I)\ge m\quad\Longrightarrow\quad
--   \widetilde H_\infty(W\mid(\mathsf{SS}(W),I))\ge m-t\log_2 n.$$
--
--   The operational recovery program is separately required to output the original set with probability one on every close honest input. No decoder, root finder, correct refinement or cost bound is assumed. This is the full computational and storage completion of the published Proved security core.
--
--   Differences from the source:
--   - reading: Step 3 says degree s-t-1 → degree less than s-t, including the zero polynomial; reason: Reed–Solomon dimension convention; over GF(3), s=2,t=1,w=w′={0,1}, the only agreeing constant is zero, and t=s also requires zero
--   - reading: storage at most t log₂ n → t field symbols, capacity log₂(n^t), and a separate packed binary length ceil(t log₂ n); reason: the paper counts field symbols and Appendix D uses log-cardinalities; for n=3,s=t=1 all three helpers occur and one bit is insufficient
--   - encoding: fixed-size sets, finite field and polynomial-time procedures → duplicate-free lists over every supplied prime-field polynomial presentation, with field quotient isomorphisms and coordinate reconstruction; reason: charges binary input and arithmetic sizes and covers every abstract finite field; constructing a canonical presentation from a bare type is outside the computation interface
--   - encoding: expected polynomial-time generation and recovery → two finite three-tape binary programs and uniform C>0,d with bound C(1+s+t+ceil(log₂ n))^d; almost-sure termination on all well-formed inputs; reason: finite local instruction semantics counts arithmetic, decoding and root finding; extended tail-sum expected time assigns infinite cost to positive-probability nontermination
--   - encoding: decoding failure has no close-input correctness promise → fail or a root set of cardinality different from s returns the received set; output lists may be in any order; reason: matches the published total recovery kernel and is unconstrained outside the promised ball; exact close-input recovery is still concluded with probability one
--   - encoding: coefficient range and s-element subsets over a universe of size n → explicit t≤s≤n with natural s,t and field cardinality n; reason: states the domain already required by the construction; no parity, characteristic, large-universe or entropy restriction is introduced
--   - generalization: the positive threshold range of the original scheme → also t=0, including s=0; reason: the same coefficient construction has an empty helper and empty product 1; the full positive range is retained
--   - generalization: auxiliary information is an arbitrary bit string → auxiliary information ranges over an arbitrary type with a PMF joint law; reason: the published security predicate includes all bit-string laws and does not assume finite auxiliary information or independence
-- source:
--   Dodis, Ostrovsky, Reyzin and Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, arXiv:cs/0602007v4 (1 Apr 2008), https://arxiv.org/abs/cs/0602007v4, Theorem 6.1, printed p.22 / PDF p.23; Construction 5, printed p.21 / PDF p.22; §6.2 standing field convention, printed p.20 / PDF p.21; Definition 3, printed p.11 / PDF p.12

import Mathlib
import Definitions.Def_FuzzyExtractors_ImprovedJSFull_Refinement

namespace FuzzyExtractors.ImprovedJSFull

open FuzzyExtractors.ImprovedJS
open FuzzyExtractors.Hamming

/-- Theorem 6.1, arXiv:cs/0602007v4, printed p.22 / PDF 23, all clauses.
Programs and polynomial constants are uniform over all field presentations
and all legal parameters. Abstract finite fields admit the presentations;
constructing a canonical presentation from a bare type is not charged to Rec.
The t=0 extension includes s=0, with empty coefficient vector and p'=1. -/
theorem theorem_6_1_full :
    ∃ (C : ℝ) (d : ℕ) (SS Rec : Program), 0 < C ∧ Deterministic SS ∧
      (∀ (F : Type) [Field F] [Fintype F], Nonempty (Presentation F)) ∧
      ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (P : Presentation F),
        P.Compact C d ∧ ∀ (s t : ℕ), t ≤ s → s ≤ Fintype.card F →
          Storage P t ∧ Implements SS Rec P C d s t ∧
          (∀ m : ℝ, IsAvgSecureSketch (sdifDist (𝓤 := F) (s := s)) m
            (m - t * Real.logb 2 (Fintype.card F)) t (sketch s t) (recover s t)) ∧
          (∀ w received : SDifS F s, sdifDist w received ≤ t →
            ∀ xs : List F, Represents xs received →
              Realizes Rec (P.recoveryInput s t xs (sketchCoeffs s t w.val))
                (fun out => ∃ ys : List F, Represents ys w ∧ out = P.encodeList ys)) := by sorry

end FuzzyExtractors.ImprovedJSFull
