-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_exponential_drawdown_crossmul
-- name    : Kyprianou.Ch08.StageB.source_result81_exponential_drawdown_crossmul
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:08:12.806529+00:00
-- url     : https://prove2.me/theorems/688ce1c6-875c-4c26-bcf4-4409c37a6c44
-- title:
--   Normalized exponentially tilted drawdown law at an arbitrary auxiliary root
-- statement:
--   Let φ be the right q-root and choose a positive offset d. At an independent exponential clock of rate ψ(φ+d), take the law of the nonnegative drawdown, weight it by exp(−φ y), and normalize. Its Laplace transform satisfies the displayed cross-multiplied equation by the original-clock Wiener–Hopf formulas above and below the positive auxiliary root, including q=0. At the auxiliary root both sides of the equation vanish.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1, tilted descending potential. Reduction of 4c63d0ad-20de-450a-9ecd-09b666951d4c.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_exponential_drawdown_crossmul
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hzero : A.ψ 0 = 0)
    (hdom : ∀ p : ℝ, 0 ≤ p → IsScaleTransformDomainBridge A.ψ p)
    (q : ℝ) (hq : 0 ≤ q) (d : ℝ) (hd : 0 < d) :
    let f : ℝ → ℝ := fun s => A.ψ (Phi A.ψ q + s) - q
    ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧ ρ (Iio (0 : ℝ)) = 0 ∧
      ∀ s : ℝ, 0 < s →
        (f d - f s) * (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
          f d * (1 - s / d) := by
  sorry
