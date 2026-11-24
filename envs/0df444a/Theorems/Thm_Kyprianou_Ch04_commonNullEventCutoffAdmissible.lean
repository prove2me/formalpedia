-- Prove2me | Theorems.Thm_Kyprianou_Ch04_commonNullEventCutoffAdmissible
-- name    : Kyprianou.Ch04.commonNullEventCutoffAdmissible
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T23:00:42.576395+00:00
-- url     : https://prove2.me/theorems/5a097bdb-4ac5-4636-aafe-ac8a342a397b
-- title:
--   Cutting off a common-null admissible Poisson kernel at a past event and an open-left time preserves admissibility and the common null property.
-- statement:
--   Cutting off a common-null admissible Poisson kernel at a past event and an open-left time preserves admissibility and the common null property.
-- source:
--   Kyprianou (2006), Corollary 4.5, corrected common-null formulation bf5da7d2-0e15-44ab-8e4a-28f5a74879e6

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Classical

theorem Kyprianou.Ch04.commonNullEventCutoffAdmissible
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (phi : Real -> Real -> Omega -> Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (hCommon : (∀ᵐ omega ∂P, ∀ (x : Real) (r : NNReal), 0 < r →
      Tendsto (fun s : Real => phi s x omega)
        (nhdsWithin (r : Real) (Set.Iio (r : Real)))
        (nhds (phi (r : Real) x omega))))
    (u : NNReal) (A : Set Omega) (hA : MeasurableSet[F u] A) :
    IsAdmissiblePoissonKernel P F (fun (s x : Real) (omega : Omega) => if (u : Real) < s ∧ omega ∈ A then phi s x omega else 0) ∧
    (∀ᵐ omega ∂P, ∀ (x : Real) (r : NNReal), 0 < r →
      Tendsto (fun s : Real => if (u : Real) < s ∧ omega ∈ A then phi s x omega else 0)
        (nhdsWithin (r : Real) (Set.Iio (r : Real)))
        (nhds (if (u : Real) < (r : Real) ∧ omega ∈ A then phi (r : Real) x omega else 0))) := by sorry
