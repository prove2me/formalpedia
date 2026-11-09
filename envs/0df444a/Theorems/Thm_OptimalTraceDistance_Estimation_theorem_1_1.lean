-- Prove2me | Theorems.Thm_OptimalTraceDistance_Estimation_theorem_1_1
-- name    : OptimalTraceDistance.Estimation.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:44:56.889163+00:00
-- url     : https://prove2.me/theorems/96735f62-3d52-4fc0-9e5e-51e90c749f1d
-- title:
--   Theorem 1.1 — optimal trace distance estimation
-- statement:
--   There is a universal $C>0$ such that for every integer $d\ge2$ and every $\varepsilon>0$, one can choose an integer $N$ and a normalized real-output quantum POVM before the two unknown states, with
--   $$N\le\left\lceil\frac{Cd^2}{\varepsilon^2\log^2d\max\{1,\varepsilon^2\log^2d\}}\right\rceil.$$
--   For every pair of positive semidefinite trace-one complex $d\times d$ matrices $\rho,\sigma$, its Born output $T$ on $\rho^{\otimes N}\otimes\sigma^{\otimes N}$ satisfies
--   $$\Pr\big[|T-\tfrac12\operatorname{tr}|\rho-\sigma||\le\varepsilon\big]\ge2/3.$$
--   The bound is a worst-case budget of $N$ copies of each state, independent of every label or tomography history. Both accuracy regimes and bounded dimensions are covered. In dimension one the distance is exactly zero and a zero-copy experiment returns zero deterministically. No rank, invertibility, commutativity or purity promise is made.
--
--   Differences from the source:
--   - encoding: Positive-dimensional complex matrices and source trace expressions → Fin d matrices; retained ordered words; real parts of real traces; explicit finite index sums; reason: Indexing and real extraction preserve all source instances; no rank or commutativity restriction is added
--   - reading: Additive-error estimation with universal big-O copy count → A ceiling bound with a state-independent POVM and success at least 2/3; reason: §5 p.21 supplies the success convention and worst-case per-input budget
--   - encoding: The construction is analyzed for d≥2 and 0<ε≤1/32 → All ε>0 and an exact d=1 zero-copy clause; reason: For 1/32<ε<1 run at 1/32, with rate ratio at most 32^4; for ε≥1 return zero; at d=1 both states equal [1] so no log denominator is evaluated
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), Theorem 1.1, p. 3; continued p.4; proof §5 p.21.

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OptimalTraceDistance.Estimation

theorem theorem_1_1 : ∃ C : ℝ, 0 < C ∧
  (∀ d : ℕ, 2 ≤ d → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, N ≤ ⌈C*rate d ε⌉₊ ∧ ∃ M : TwoStateMeasurement d N,
      ∀ (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ),
        ENNReal.ofReal (2/3 : ℝ) ≤
          outcomeLaw M ρ σ hρ hσ {x | |x-distance ρ σ| ≤ ε}) ∧
  (∃ M : TwoStateMeasurement 1 0, ∀ (ρ σ : Mat 1) (hρ : Density ρ) (hσ : Density σ),
    distance ρ σ = 0 ∧ outcomeLaw M ρ σ hρ hσ = Measure.dirac 0) := by sorry

end OptimalTraceDistance.Estimation
