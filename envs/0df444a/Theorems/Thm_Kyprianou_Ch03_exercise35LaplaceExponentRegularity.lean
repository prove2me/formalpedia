-- Prove2me | Theorems.Thm_Kyprianou_Ch03_exercise35LaplaceExponentRegularity
-- name    : Kyprianou.Ch03.exercise35LaplaceExponentRegularity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:48:46.43711+00:00
-- url     : https://prove2.me/theorems/d88a3442-e2a1-4006-a3b5-6b95c603b071
-- title:
--   Exercise 3.5: smoothness, convexity and exceptional pure-drift cases
-- statement:
--   Corrects the textbook's unqualified strict convexity and asymptotic claims. Pure positive drift is affine, negative subordinators need not have psi tending to plus infinity, and smoothness at zero may fail for heavy negative jump tails.
-- source:
--   Kyprianou (2006), Exercise 3.5, printed p. 84; solution printed pp. 314-315.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem exercise35LaplaceExponentRegularity
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) :
    L.ψ 0 = 0 ∧
    ContDiffOn ℝ (⊤ : WithTop ℕ∞) L.ψ (Set.Ioi 0) ∧
    ConvexOn ℝ (Set.Ici 0) L.ψ ∧
    ((0 < L.σ ∨ L.ν ≠ 0) →
      StrictConvexOn ℝ (Set.Ioi 0) L.ψ) ∧
    ((¬ (∀ᵐ omega : Omega ∂P,
        Antitone (fun t : NNReal => L.X t omega))) →
      Tendsto L.ψ atTop atTop) := by
  sorry

end Kyprianou.Ch03
