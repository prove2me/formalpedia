-- Prove2me | Theorems.Thm_LIPAlgorithm_lemma_4_5
-- name    : LIPAlgorithm.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:22.183728+00:00
-- url     : https://prove2.me/theorems/9cb4c142-467a-4a18-b4f8-1cb1558ad37c
-- title:
--   Lemma 4.5 — global heat upper bound
-- statement:
--   There is an absolute constant $C'>0$ such that for every $C>0$ there is $n_0$ with the following property. For $n\ge n_0$, a rank-$n$ well-rounded lattice $L$ with $\lambda=\lambda_1(L)$, $1\le j\le n$, $t=8\sqrt n/\lambda$ and $s=Cn^2\log n/\lambda$,
--
--   $$\mathbb E_{W\sim D_{L^*,s}}[\Delta_j(W)]\le C'\,\frac{t^2j\lambda\sqrt n}{s}.$$
--
--   Compared with Lemma 4.4, this bounds the probability of ambiguity at every rank.
--
--   Differences from the source:
--   - reading: O(t²jλ√n/s) → an explicit C′ placed before C; reason: the proof of Theorem 4.6 states that the implied constants do not depend on C
--   - reading: 'for sufficiently large n' (p.8) with the absolute constant C in s → absolute constants, then C, then n₀(C), then n and L; reason: n₀ must depend on C: at n = 1, s = 0, and the proof needs s ≥ 2t
--   - reading: log n with no named base → Real.logb 2; reason: a change of base only rescales C in s; base 2 gives the smaller threshold r*(n)
--   - encoding: expectation and probability over D_{L*,s} → a tsum of the masses of the published discreteGaussian over dual L; reason: the sums converge since the masses are Gaussian weights and the summands grow polynomially; same value
--   - generalization: C a sufficiently large absolute constant (§4, p.21; 'C is chosen large', p.22) → every C > 0, with n₀ after C; reason: the proof needs only s ≥ 2t and ε·s²/t² ≤ 2^{−n}·poly(n), which hold for n ≥ n₀(C) at every C > 0; the source's range of C is a sub-range
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Lemma 4.5, p.22; parameters §4, pp.21–22

import Mathlib
import Definitions.Def_LIPAlgorithm_heatDelta

namespace LIPAlgorithm

/-- **Lemma 4.5 (Global heat upper bound).** Aggarwal, Jiang, Li, Liu, STOC 2027 submission (manuscript sha256 61ee52aa…),
Lemma 4.5, p.22 (PDF p.25), with `t = 8√n/λ` (p.22) and `s = C·n²·log n/λ` (p.21): for `W ∼ D_{L*,s}`,
`E_W[Δ_j(W)] ≤ O(t²jλ√n/s)`.

**Formalization Note.** The implied constant `C'` is placed before `C` (the proof of Theorem 4.6, p.24: the implied constants
"do not depend on C"), and `n₀` after `C` ("all asymptotic statements … hold for sufficiently large n", p.8). -/
theorem lemma_4_5 :
    ∃ C' : ℝ, 0 < C' ∧ ∀ C : ℝ, 0 < C → ∃ n₀ : ℕ,
      ∀ (n : ℕ) (L : Submodule ℤ (E n)) [DiscreteTopology L] [IsZLattice ℝ L] (j : ℕ),
        n₀ ≤ n → IsWellRounded L → 1 ≤ j → j ≤ n →
          gaussExp L (scaleS C L) (heatDelta L j (scaleT L)) ≤
            C' * scaleT L ^ 2 * j * RegevLWE.SmoothingLB.lambda1 L * Real.sqrt n / scaleS C L := by sorry

end LIPAlgorithm
