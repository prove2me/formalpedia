-- Prove2me | Theorems.Thm_LIPAlgorithm_theorem_4_6
-- name    : LIPAlgorithm.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:48.429473+00:00
-- url     : https://prove2.me/theorems/250cecff-cf9d-43f3-a5ea-c4f31fd8ca1f
-- title:
--   Theorem 4.6 — probability that a rank is ambiguous
-- statement:
--   There is an absolute constant $c_0>0$, independent of $C$, such that for every $C>0$ there is $n_0$ with the following property. For $n\ge n_0$, a rank-$n$ well-rounded lattice $L$, $\lambda=\lambda_1(L)$, $s=Cn^2\log n/\lambda$ and $W\sim D_{L^*,s}$, for every $j\in[n]$,
--
--   $$\Pr[j\text{ is ambiguous at }W]\le\frac{c_0\,j}{C\,n\log n},\qquad\text{and consequently}\qquad \mathbb E[\mathrm{Amb}(W)]\le\frac{c_0\,n}{C\log n}.$$
--
--   This is the core probabilistic estimate of the paper: a random dual vector leaves few ambiguous ranks.
--
--   Differences from the source:
--   - reading: 'for sufficiently large n' (p.8) with the absolute constant C in s → absolute constants, then C, then n₀(C), then n and L; reason: n₀ must depend on C: at n = 1, s = 0, and the proof needs s ≥ 2t
--   - reading: log n with no named base → Real.logb 2; reason: a change of base only rescales C in s; base 2 gives the smaller threshold r*(n)
--   - encoding: expectation and probability over D_{L*,s} → a tsum of the masses of the published discreteGaussian over dual L; reason: the sums converge since the masses are Gaussian weights and the summands grow polynomially; same value
--   - generalization: C a sufficiently large absolute constant (§4, p.21; 'C is chosen large', p.22) → every C > 0, with n₀ after C; reason: the proof needs only s ≥ 2t and ε·s²/t² ≤ 2^{−n}·poly(n), which hold for n ≥ n₀(C) at every C > 0; the source's range of C is a sub-range
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Theorem 4.6, p.24

import Mathlib
import Definitions.Def_LIPAlgorithm_heatDelta

namespace LIPAlgorithm

/-- **Theorem 4.6 (Probability that a rank is ambiguous).** Aggarwal, Jiang, Li, Liu, STOC 2027 submission (manuscript sha256
61ee52aa…), Theorem 4.6, p.24 (PDF p.27). With `s = C·n²·log n/λ` and `W ∼ D_{L*,s}`, for every `j ∈ [n]`,
`Pr[j is ambiguous at W] ≤ c₀·j/(C·n·log n)`, and `E[Amb(W)] ≤ c₀·n/(C·log n)`.

**Formalization Note.** `c₀` is before `C`, which is the printed "independent of C", and `n₀` is after `C` (p.8): at `n = 1`,
`s = 0`. -/
theorem theorem_4_6 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ C : ℝ, 0 < C → ∃ n₀ : ℕ,
      ∀ (n : ℕ) (L : Submodule ℤ (E n)) [DiscreteTopology L] [IsZLattice ℝ L],
        n₀ ≤ n → IsWellRounded L →
          (∀ j : ℕ, 1 ≤ j → j ≤ n →
            gaussProb L (scaleS C L) {w | Ambiguous L j (w : E n)} ≤
              c₀ * j / (C * n * Real.logb 2 n)) ∧
          gaussExp L (scaleS C L) (fun w => (ambCount L w : ℝ)) ≤ c₀ * n / (C * Real.logb 2 n) := by sorry

end LIPAlgorithm
