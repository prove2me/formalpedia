-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteENNCompensatedMartingale
-- name    : Kyprianou.Ch04.finiteENNCompensatedMartingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:26:58.683519+00:00
-- url     : https://prove2.me/theorems/c26c0933-689e-44ba-866a-36cf01cb204c
-- title:
--   A strongly adapted real difference of two finite-expectation nonnegative processes is a martingale if their expected cumulative differences balance on every past event.
-- statement:
--   A strongly adapted real difference of two finite-expectation nonnegative processes is a martingale if their expected cumulative differences balance on every past event.
-- source:
--   Kyprianou (2006), first edition, numbered result 4.6, printed page 97.; correction of the formalisation of 61a5bc8c-34e9-49c2-b76f-9c0e0650fed4. Corrects the remaining exceptional-outcome measurability defect in AdaptedV2.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem finiteENNCompensatedMartingale
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (R C : NNReal → Omega → ENNReal) (M : NNReal → Omega → Real)
    (hR : ∀ t, Measurable (R t)) (hC : ∀ t, Measurable (C t))
    (hRf : ∀ t, (∫⁻ w, R t w ∂P) ≠ ⊤)
    (hCf : ∀ t, (∫⁻ w, C t w ∂P) ≠ ⊤)
    (hAdapt : StronglyAdapted F M)
    (hM : ∀ t, M t =ᵐ[P] fun w => (R t w).toReal - (C t w).toReal)
    (hBalance : ∀ u t : NNReal, u ≤ t → ∀ A : Set Omega, MeasurableSet[F u] A →
      (∫⁻ w in A, R u w ∂P) + (∫⁻ w in A, C t w ∂P) =
      (∫⁻ w in A, R t w ∂P) + (∫⁻ w in A, C u w ∂P)) :
    Martingale M F P := by
  sorry
end Kyprianou.Ch04
