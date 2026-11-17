-- Prove2me | Theorems.Thm_MantriCVQ_Supplement_theorem_7_4
-- name    : MantriCVQ.Supplement.theorem_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:09:32.973715+00:00
-- url     : https://prove2.me/theorems/6f3dd129-3789-407d-b3c6-a6f57fd72083
-- title:
--   Theorem 7.4 — with noisy code tables: bounded-error quantum evaluation, a $0.99/0.01$ public-coin proof, and no constant-depth circuits of size $2^{\mathrm{poly}(n)}$
-- statement:
--   Fix a code family $C$ of Definition 3.1, a noise rate $0\le\eta<1/4$, and a height function $h$. Consider instances of size $n$ and height $h(n)$, stored in the oracle at the addresses $1^n0w$, in which every code table is within relative distance $\eta$ of a codeword.
--
--   1. A uniform polynomial-time bounded-error quantum algorithm computes the root value: on input $1^n$ it accepts with probability at least $2/3$ when the root value is $1$ and at most $1/3$ when it is $0$.
--   2. A public-coin interactive proof system verifies the root value with completeness at least $0.99$, soundness error at most $0.01$ against computationally unbounded provers, an efficient honest prover, and polynomially many messages.
--   3. No family of constant-depth circuits of size $2^{\mathrm{poly}(n)}$ computes the root value on every such instance.
--
--   Hence, for every oracle that stores such an instance at every size, the unary language of inputs $1^n$ whose instance has root value one is in $\mathsf{BQP}^O$, has such a proof system, and is not computed by constant-depth circuits of size $2^{\mathrm{poly}(n)}$: the separation of Theorem 1.3 tolerates noisy code tables.
--
--   **Formalization Note** One algorithm, one verifier and one honest prover work for every oracle and every size $n\ge1$, and each guarantee at $n$ assumes only that the instance of size $n$ is valid with noise rate $\eta$. The lower bound is for non-uniform circuit families of constant depth $D$ and size at most $2^{q(n)}$, and produces a size $n\ge1$ and an instance valid with noise rate $\eta$ on which the circuit of size $n$ errs.
--
--   Differences from the source:
--   - encoding: instances in which every code table is within relative distance η of a codeword → ValidNoisy C η of the instance of size n and height h(n), stored in the oracle at 1^n 0 w; within means ≤ η; reason: §7.4's definition; for η = 0 it is the exact validity
--   - encoding: a uniform polynomial-time bounded-error quantum algorithm computes the root value → a uniform polynomial-size ExactFamily over G whose acceptance probability on 1^n is ≥ 2/3 when the root value is 1 and ≤ 1/3 when it is 0; reason: §3.1's BQP convention (error at most 1/3); the circuit family structure carries no exactness condition
--   - reading: the algorithm and the proof system are for instances of size n (input 1^n) → guarantees on input 1^n for n ≥ 1, for every oracle whose instance of size n is valid with noise rate η; one algorithm, verifier and prover for all oracles; reason: the paper's proof (p. 41) uses one algorithm and one protocol for every such oracle; inputs other than 1^n are not part of the statement
--   - encoding: polynomially many messages; an efficient honest prover → a PCVerifier (whose slot count is bounded by a polynomial) and a uniform polynomial-size QProver over G; reason: PCVerifier.S_le bounds the slots; the verifier is polynomial-time by construction
--   - generalization: soundness against computationally unbounded provers, classical or quantum, that communicate classically → soundness against every map from input and transcript to a distribution on the next message; reason: every such prover induces these conditional laws, so the class of strategies contains all of them
--   - encoding: no family of constant-depth circuits of size 2^{poly(n)} computes the root value on every such instance → for every D, polynomial q and family F_n of depth ≤ D and size ≤ 2^{q(n)} on the leaves, there are n ≥ 1 and a leaf table valid with noise rate η on which F_n differs from the root value; reason: the negation of computing on every instance; size is gates plus wires as in the base mission
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem 7.4, p. 41 (PDF p. 43); noisy validity on p. 41; proof on p. 41 (PDF p. 43)

import Mathlib
import Definitions.Def_MantriCVQ_Supplement_HeightFunction
import Definitions.Def_MantriCVQ_Supplement_nodeValNoisy
import Definitions.Def_MantriCVQ_Admissible
import Definitions.Def_MantriCVQ_CodeFamily
import Definitions.Def_MantriCVQ_ExactFamily
import Definitions.Def_MantriCVQ_ACCircuit
import Definitions.Def_MantriCVQ_Addr
import Definitions.Def_MantriCVQ_dimsRange
import Definitions.Def_MantriCVQ_leafTable
import Definitions.Def_MantriCVQ_acceptProb
import Definitions.Def_MantriCVQ_QProver

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ.Supplement

open MantriCVQ

/-- **Theorem 7.4** (Evaluation and verification with noisy code tables; Mantri, arXiv:2610.37635 (PDF
sha256 d1fab777…1d0b33), Theorem 7.4, p. 41 (PDF p. 43)): fix a code family of Definition 3.1, a
noise rate `0 ≤ η < 1/4` and a height function `h`. For instances of size `n` and height `h(n)` in
which every code table is within relative distance `η` of a codeword, a uniform polynomial-time
bounded-error quantum algorithm computes the root value, and a public-coin interactive proof system
verifies it with completeness at least `0.99`, soundness error at most `0.01` against computationally
unbounded provers, an efficient honest prover, and polynomially many messages. No family of
constant-depth circuits of size `2^{poly(n)}` computes the root value on every such instance.

**Formalization Note** The instance of size `n` is read through the oracle at the addresses `1^n 0 w`
(§7.1) and the input is `1^n`, `n ≥ 1`. One algorithm, one verifier and one honest prover serve every
oracle and every `n`; each guarantee at `n` assumes only that the instance of size `n` is valid with
noise rate `η`. Bounded error is the paper's `BQP` convention (§3.1): acceptance probability at least
`2/3` when the root value is `1` and at most `1/3` when it is `0`. "Polynomially many messages" holds
for every `PCVerifier` (its slot count is bounded by a polynomial, `PCVerifier.S_le`), and the verifier
is polynomial-time by construction. In the lower bound the circuits are non-uniform, of depth at most
a constant `D` and size at most `2^{q(n)}` for a polynomial `q`, on the leaves of the instance of size
`n` and height `h(n)`; the conclusion is a size `n ≥ 1` and a leaf table valid with noise rate `η` on
which the circuit of size `n` differs from the root value. -/
theorem theorem_7_4 {G : List Gate} (hG : Admissible G) {d : ℕ} (C : CodeFamily G d)
    (η : ℝ) (hη0 : 0 ≤ η) (hη : η < 1 / 4) (h : ℕ → ℕ) (hh : HeightFunction h) :
    (∃ F : ExactFamily G, F.Uniform ∧ F.PolyBounded ∧
      ∀ (O : Oracle) (n : ℕ), 1 ≤ n →
        ValidNoisy C.code η (dimsRange n 0 (h n)) (leafTable O n) [] →
        (nodeValNoisy C.code η (dimsRange n 0 (h n)) (leafTable O n) [] = true →
            (2 : ℝ) / 3 ≤ F.acceptProb O (unary n)) ∧
        (nodeValNoisy C.code η (dimsRange n 0 (h n)) (leafTable O n) [] = false →
            F.acceptProb O (unary n) ≤ 1 / 3)) ∧
    (∃ (V : PCVerifier) (P : QProver G), P.Uniform ∧ P.PolyBounded ∧
      ∀ (O : Oracle) (n : ℕ), 1 ≤ n →
        ValidNoisy C.code η (dimsRange n 0 (h n)) (leafTable O n) [] →
        (nodeValNoisy C.code η (dimsRange n 0 (h n)) (leafTable O n) [] = true →
            (99 : ℝ) / 100 ≤ acceptProb O V (P.toStrategy O) (unary n)) ∧
        (nodeValNoisy C.code η (dimsRange n 0 (h n)) (leafTable O n) [] = false →
            ∀ σ : Strategy, acceptProb O V σ (unary n) ≤ 1 / 100)) ∧
    ∀ (D : ℕ) (q : Polynomial ℕ) (F : (n : ℕ) → ACCircuit (Addr (dimsRange n 0 (h n)))),
      (∀ n : ℕ, (F n).depth ≤ D) → (∀ n : ℕ, (F n).size ≤ 2 ^ q.eval n) →
      ∃ n : ℕ, 1 ≤ n ∧ ∃ Y : Str → Bool,
        ValidNoisy C.code η (dimsRange n 0 (h n)) Y [] ∧
        (F n).eval (fun a => Y (Addr.toStr _ a)) ≠
          nodeValNoisy C.code η (dimsRange n 0 (h n)) Y [] := by sorry

end MantriCVQ.Supplement
