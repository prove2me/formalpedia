-- Prove2me | Theorems.Thm_NCPComm_Supplement_theorem_1_3
-- name    : NCPComm.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:18:41.115616+00:00
-- url     : https://prove2.me/theorems/818dacb8-d96b-4cf7-a33f-577c20ea5760
-- title:
--   Theorem 1.3 — tolerant identity verification with $o(\min\{1/\|D\|_2^2, N\|D\|_2\})$ samples communicates $\Omega(N\|D\|_2^2)$ bits
-- statement:
--   Fix an exponent $k\in(\tfrac12,1)$. There are constants $0<a\le b$ and $c_0>0$, depending only on $k$, with the following property. For each $N$, let $Q\mapsto\Pi_{N,Q}$ be a tolerant identity verification protocol over $[N]$ with completeness threshold $\delta_c=1/16$ and soundness threshold $\delta_f=5/64$, both errors at most $1/3$, whose verifier is given the explicit reference distribution $Q$ and draws $s(N)$ samples from the unknown distribution $D$; suppose that, for all large $N$, it is correct on every input pair $(D,Q)$ with
--   $$
--   a\,N^{-k}\le\|D\|_2^2\le b\,N^{-k},\qquad a\,N^{-k}\le\|Q\|_2^2\le b\,N^{-k},
--   $$
--   that is, at collision probability $\Theta(N^{-k})$. Then:
--
--   1. if $s(N)=o\big(\min\{N^{k},\,N^{1-k/2}\}\big)$, equivalently $s(N)=o\big(\min\{1/\|D\|_2^2,\;N\|D\|_2\}\big)$ at this scale, then for all large $N$ there is a reference distribution $Q$ with $a\,N^{-k}\le\|Q\|_2^2\le b\,N^{-k}$ on which the protocol communicates
--   $$
--   c(N)\ \ge\ c_0\,N^{1-k}\qquad\big(=\Omega(N\|D\|_2^2)\big)\ \text{bits};
--   $$
--   2. in particular the same bound holds whenever $s(N)=O(\sqrt N)$, the optimal verifier sample complexity.
--
--   The bound is a worst case over the hard input pairs $(D,Q)$ at the given collision-probability scale, not a bound for every pair. It transfers the Noisy Collisions lower bound $\Omega(N/K)$ (Corollary 4.8, eq. (1)) to a label-sensitive task, and together with Proposition 5.1 shows that the paper's interactive proof for tolerant identity verification is communication-optimal.
--
--   **Formalization Note** Communication is the depth of the bit tree run with reference $Q$; the protocol may depend arbitrarily on $Q$. The verifier draws exactly $s(N)$ i.i.d. samples before the interaction (a verifier using fewer ignores the rest). The constants $a,b,c_0$ are quantified before the protocol family.
--
--   Differences from the source:
--   - reading: "every collision probability ‖D‖₂² of order a fixed power of N strictly between N^{−1} and N^{−1/2}" → for each fixed k ∈ (1/2, 1), the band a·N^{−k} ≤ ‖D‖₂² ≤ b·N^{−k} with a, b > 0 (and c₀) existential, depending only on k, quantified before the protocol family; reason: "of order N^{−k}" names a Θ class, and correctness is only assumed on one such band, which is the weaker hypothesis and therefore the stronger of the readings; the proof's hard pairs have ‖Q′‖₂² between 49/(256K) and 1/(4K) + O(1/N) with K = Θ(N^k)
--   - reading: worst-case communication over the hard pairs (D, Q) at the scale (footnote 4) → correctness required only on the pairs with both D and Q in the band, and the conclusion that some reference Q in the band has depth at least c₀·N^{1−k}; reason: footnote 4 and p.32 ("c(N) its maximum communication over the mixture instances", whose Q and Q′ both have squared norm Θ(1/K)); this is the stronger of the readings: a protocol correct for every Q (or every D) is correct on these pairs, and a Q in the band is a Q
--   - encoding: s(N) = o(min{1/‖D‖₂², N‖D‖₂}) and the bound Ω(N‖D‖₂²) → s(N)/min{N^k, N^{1−k/2}} → 0 and c₀·N^{1−k}; reason: on the band these quantities are within constant factors (depending on a, b) of each other, which o(·) and Ω(·) absorb
--   - encoding: "O(√N) verifier samples" → ∃ C, eventually s(N) ≤ C·√N; reason: definition of O(·)
--   - encoding: Ω(·) and all hypotheses "for all sufficiently large N" → eventually in N (Filter.atTop); reason: asymptotic statements
--   - generalization: a probabilistic polynomial-time verifier with sample access making up to s(N) adaptive requests (Definition 3.4) → an unbounded verifier holding s(N) i.i.d. samples up front, a PMF over deterministic behaviours chosen from the sample, with secret coins; reason: adaptive requests are served from the list; a lower bound over all verifiers implies the one over efficient ones
--   - generalization: a prover with sample access to D and the explicit Q → a strategy chosen after (D, Q): a PMF over deterministic behaviours for completeness, any deterministic behaviour for soundness; reason: more protocols pass completeness, so the class covered is larger; soundness against all deterministic behaviours chosen knowing D covers every sample-access cheating prover (acceptance is linear in mixtures)
--   - generalization: Q given as an explicit string of size N·log N → Q any PMF on Fin N, the protocol (verifier, speaker, depth) an arbitrary function of Q; reason: every protocol reading the explicit description is one of these
--   - encoding: communication: total bits exchanged on the worst run → the depth of the bit tree with a speaker function (published NCPComm.IPProtocol); reason: a protocol of worst-case communication at most c is one after padding
--   - encoding: δ_TV(D, Q) → OAI.ThreeState.tvMass D Q = ½∑ₓ|D(x) − Q(x)|; labels [N] → Fin N; reason: Lean convention; the same quantity on a finite domain
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Theorem 1.3, p.5 (footnote 4); proved in §4.3, pp.31–33

import Mathlib
import Definitions.Def_NCPComm_Supplement_IsTolerantIdentityVerifier

open scoped NNReal ENNReal Topology
open Filter

namespace NCPComm.Supplement

/-- **Theorem 1.3 (Communication lower bound for tolerant identity verification), p.5**, proved in
§4.3, pp.31–33 (Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027
submission, manuscript sha256 714c0353…). Fix `k ∈ (1/2, 1)`. There are constants `0 < a ≤ b` and
`c₀ > 0` such that every family of tolerant identity verifiers (`δ_c = 1/16`, `δ_f = 5/64`, both
errors at most `1/3`) that is correct on the input pairs `(D, Q)` at the scale
`a·N^{−k} ≤ ‖D‖₂², ‖Q‖₂² ≤ b·N^{−k}` and uses `s(N)` samples has, for all large `N`, a reference
distribution `Q` at that scale on which it communicates at least `c₀·N^{1−k}` (`= Ω(N‖D‖₂²)`) bits, provided
(1) `s(N) = o(min{N^k, N^{1−k/2}})` (`= o(min{1/‖D‖₂², N‖D‖₂})` at that scale), or
(2) `s(N) = O(√N)`.

**Formalization Note** `‖D‖₂² = Θ(N^{−k})` is the band `[a·N^{−k}, b·N^{−k}]` with `a, b`
existential and quantified before the protocol family, like `c₀`; the constants depend only on `k`.
On the band, `1/‖D‖₂²`, `N‖D‖₂` and `N‖D‖₂²` are within constant factors of `N^k`, `N^{1−k/2}` and
`N^{1−k}`, so the sample condition and the bound are written with these powers. Communication is the
depth of the bit tree run with reference `Q`, and the worst case over the hard pairs (footnote 4) is
the existence of a `Q` in the band with large depth. Correctness is only required on the pairs with
both `D` and `Q` in the band, for all large `N`; since a protocol correct for every `Q` is correct on
these pairs, and a `Q` in the band is a `Q`, this covers both readings of "pairs at the scale". -/
theorem theorem_1_3 (k : ℝ) (hk₁ : 1 / 2 < k) (hk₂ : k < 1) :
    ∃ a b c₀ : ℝ, 0 < a ∧ a ≤ b ∧ 0 < c₀ ∧
      ∀ (s : ℕ → ℕ) (P : ∀ N : ℕ, PMF (Fin N) → NCPComm.IPProtocol N),
        (∀ᶠ N : ℕ in atTop, IsTolerantIdentityVerifier (P N) (s N)
          (collisionBand a b k N) (collisionBand a b k N)) →
        (Tendsto (fun N : ℕ => (s N : ℝ) / min ((N : ℝ) ^ k) ((N : ℝ) ^ (1 - k / 2)))
            atTop (𝓝 0) →
          ∀ᶠ N : ℕ in atTop, ∃ Q ∈ collisionBand a b k N,
            c₀ * (N : ℝ) ^ (1 - k) ≤ ((P N Q).depth : ℝ)) ∧
        ((∃ C : ℝ, ∀ᶠ N : ℕ in atTop, (s N : ℝ) ≤ C * Real.sqrt N) →
          ∀ᶠ N : ℕ in atTop, ∃ Q ∈ collisionBand a b k N,
            c₀ * (N : ℝ) ^ (1 - k) ≤ ((P N Q).depth : ℝ)) := by sorry

end NCPComm.Supplement
