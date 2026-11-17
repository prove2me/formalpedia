-- Prove2me | Theorems.Thm_Kyprianou_Ch07_ruinIntegratedTailAsymptotic
-- name    : Kyprianou.Ch07.ruinIntegratedTailAsymptotic
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T21:23:07.968553+00:00
-- url     : https://prove2.me/theorems/446c4b68-86bb-4777-9fce-cee69dcb7158
-- title:
--   Theorem 7.16(i): ruin probability asymptotic to integrated Lévy tail
-- statement:
--   Prove the spectrally positive ruin probability equivalent to its integrated Lévy jump tail divided by the magnitude of the negative mean, under original regular variation assumptions.
-- source:
--   Kyprianou (2006), Chapter 7, Theorem 7.16 parts (i) and (ii), printed p. 204; original PDF p. 213. Exact standalone source conjunct of published Chapter 7 theorem 356dccb0-7890-47ae-8c8c-17297f2edcfa.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.ruinIntegratedTailAsymptotic
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X Xleft : NNReal → Omega → Real)
    (b : Real) (sigma2 : NNReal) (Pi : Measure Real)
    (alpha : Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi)
    (hSpectralPositive : Pi (Set.Iio 0) = 0)
    (hLeft : Kyprianou.Ch05.IsLeftLimitVersion P X Xleft)
    (hAlpha : 0 < alpha)
    (hMeanFinite : Integrable (X 1) P)
    (hMeanNegative : (∫ omega, X 1 omega ∂P) < 0)
    (hRegularTail : Kyprianou.Ch05.RegularlyVaryingAtInfinity
      (fun x : Real => (Pi (Set.Ioi x)).toReal) (-(alpha + 1))) :
    let lifetime : Omega → WithTop NNReal := fun _ => ⊤
    let ruin : Real → Set Omega := fun x =>
      {omega | Kyprianou.Ch05.PassageFinite X lifetime x omega}
    let overshoot : Real → Omega → Real := fun x omega =>
      Kyprianou.Ch05.passageOvershoot X lifetime x omega
    let prejump : Real → Omega → Real := fun x omega =>
      Xleft (Kyprianou.Ch05.passageFiniteTime X lifetime x omega) omega
    let integratedTail : Real → Real := fun x =>
      ∫ y : Real in Set.Ioi x, (Pi (Set.Ioi y)).toReal ∂volume
    (Tendsto (fun x : Real =>
       (P (ruin x)).toReal / integratedTail x)
       atTop (nhds (1 / |∫ omega, X 1 omega ∂P|))) := by
  sorry
