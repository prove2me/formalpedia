-- Prove2me | Theorems.Thm_Kyprianou_Ch04_chapterFourMainResultsV4
-- name    : Kyprianou.Ch04.chapterFourMainResultsV4
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T08:10:59.369983+00:00
-- url     : https://prove2.me/theorems/607c0746-420a-527c-b3fa-08993b451930
-- title:
--   Chapter 4 cumulative goal: all 21 current milestones (corrected V4)
-- statement:
--   Cumulative conjunction of the 21 current Chapter 4 milestone propositions. Replaces the obsolete Corollary 4.6 with its V3 statement including local finiteness of spanning sets; replaces the Exercise 4.4 and Exercise 4.5 certificates with their current V3 versions. All other obligations are retained verbatim from the previous capstone. Exercise 4.5 requires the actual characteristic triplet.
-- source:
--   Kyprianou (2006), Chapter 4, pp. 83–109

import Mathlib
import Definitions.Def_Kyprianou_Ch04_CompensationCertificationV3
import Definitions.Def_Kyprianou_Ch04_Exercise4_1CertificationV2
import Definitions.Def_Kyprianou_Ch04_Exercise4_2Certification
import Definitions.Def_Kyprianou_Ch04_Exercise4_3Certification
import Definitions.Def_Kyprianou_Ch04_Exercise4_4CertificationV3
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Definitions.Def_Kyprianou_Ch04_Exercise4_6Certification
import Definitions.Def_Kyprianou_Ch04_Exercise4_7Certification
import Definitions.Def_Kyprianou_Ch04_Exercise4_8CertificationV2
import Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Cumulative Chapter 4 capstone with current corrected compensation and exercise certificates. -/
theorem chapterFourMainResultsV4 :
    certificate_4_1_v2 ∧
    certificate_4_2_v2 ∧
    certificate_4_3_v2 ∧
    certificate_4_4_v3 ∧
    certificate_4_5_v3 ∧
    (∀
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (phi : Real -> Real -> Omega -> Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (hCommon : ∀ᵐ omega ∂P, ∀ (x : Real) (t : NNReal), 0 < t →
      Tendsto (fun s : Real => phi s x omega)
        (nhdsWithin (t : Real) (Set.Iio (t : Real)))
        (nhds (phi (t : Real) x omega)))
    (hPast : ∀ (t : NNReal) (B : Set (Real × Real)),
      MeasurableSet B →
      B ⊆ Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ →
      Measurable[F t] (fun omega => N.N omega B))
    (hKernelPast : ∀ t : NNReal,
      Measurable[(F t).prod inferInstance]
        (fun z : Omega × (Real × Real) =>
          if z.2.1 ∈ Set.Icc (0 : Real) (t : Real)
          then phi z.2.1 z.2.2 z.1 else 0))
    (hLocalFinite : ∀ (t : NNReal) (n : Nat) (omega : Omega),
      N.N omega (Set.Icc (0 : Real) (t : Real) ×ˢ spanningSets levyMeasure n) ≠ ⊤)
    (hFinite : forall t : NNReal,
      (∫⁻ omega,
        (∫⁻ s in Set.Icc (0 : Real) (t : Real),
          (∫⁻ x, ENNReal.ofReal (phi s x omega) ∂levyMeasure)
          ∂volume) ∂P) < ⊤),
    MeasureTheory.Martingale
      (fun (t : NNReal) omega =>
        (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
          phi z.1 z.2 omega ∂(N.N omega)) -
        (∫ s in Set.Icc (0 : Real) (t : Real),
          (∫ x, phi s x omega ∂levyMeasure) ∂volume))
      F P ) ∧
    certificate_4_7_v2 ∧
    certificate_4_8_v2 ∧
    certificate_4_9_v2 ∧
    certificate_4_10_v2 ∧
    certificate_4_11_v2 ∧
    certificate_4_12_v2 ∧
    certificate_exercise_4_1_v2 ∧
    certificate_exercise_4_2 ∧
    certificate_exercise_4_3 ∧
    certificate_exercise_4_4_v3 ∧
    certificate_exercise_4_5V3 ∧
    certificate_exercise_4_6 ∧
    certificate_exercise_4_7 ∧
    certificate_exercise_4_8_v2 ∧
    certificate_exercise_4_9 := by
  sorry
end Kyprianou.Ch04
