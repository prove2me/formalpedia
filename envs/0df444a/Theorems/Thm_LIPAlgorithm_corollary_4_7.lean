-- Prove2me | Theorems.Thm_LIPAlgorithm_corollary_4_7
-- name    : LIPAlgorithm.corollary_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:34.776204+00:00
-- url     : https://prove2.me/theorems/a4e41d0b-404e-4b3b-9c2b-d14b2024d88d
-- title:
--   Corollary 4.7 — resolving markers
-- statement:
--   There is an absolute constant $C_0>0$ such that for every $C\ge C_0$ there is $n_0$ with the following property. For $n\ge n_0$, a rank-$n$ well-rounded lattice $L$ and $s=Cn^2\log n/\lambda_1(L)$, with probability at least $0.99$ over $W\sim D_{L^*,s}$ the residual rank $n-|J(W)|$ is at most $2n/\log n$; the same holds for $W\sim D_{L^*,s/\sqrt2}$.
--
--   A marker with this property is what the birthday algorithm collects.
--
--   Differences from the source:
--   - reading: 'C ≥ 100c₀', and 'after increasing the absolute constant' for s/√2 → one absolute C₀ for both clauses; reason: the two thresholds are absolute constants, and their maximum serves both
--   - reading: 'for sufficiently large n' (p.8) with the absolute constant C in s → absolute constants, then C, then n₀(C), then n and L; reason: n₀ must depend on C: at n = 1, s = 0, and the proof needs s ≥ 2t
--   - reading: log n with no named base → Real.logb 2; reason: a change of base only rescales C in s; base 2 gives the smaller threshold r*(n)
--   - encoding: expectation and probability over D_{L*,s} → a tsum of the masses of the published discreteGaussian over dual L; reason: the sums converge since the masses are Gaussian weights and the summands grow polynomially; same value
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Corollary 4.7, p.24

import Mathlib
import Definitions.Def_LIPAlgorithm_heatDelta

namespace LIPAlgorithm

/-- **Corollary 4.7 (Resolving markers).** Aggarwal, Jiang, Li, Liu, STOC 2027 submission (manuscript sha256 61ee52aa…),
Corollary 4.7, p.24 (PDF p.27). Once `C` is at least an absolute constant, with probability at least `0.99` over `W ∼ D_{L*,s}`
the residual rank `n − |J(W)|` is at most `2n/log n`, and the same holds for `W ∼ D_{L*,s/√2}`.

**Formalization Note.** `C₀` covers the printed `C ≥ 100c₀` and the "increasing the absolute constant" for `s/√2`; `n₀` is after
`C` (p.8). -/
theorem corollary_4_7 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∃ n₀ : ℕ,
      ∀ (n : ℕ) (L : Submodule ℤ (E n)) [DiscreteTopology L] [IsZLattice ℝ L],
        n₀ ≤ n → IsWellRounded L →
          (99 / 100 : ℝ) ≤ gaussProb L (scaleS C L)
              {w | (n : ℝ) - (fixedSteps L (w : E n)).card ≤ 2 * n / Real.logb 2 n} ∧
          (99 / 100 : ℝ) ≤ gaussProb L (scaleS C L / Real.sqrt 2)
              {w | (n : ℝ) - (fixedSteps L (w : E n)).card ≤ 2 * n / Real.logb 2 n} := by sorry

end LIPAlgorithm
