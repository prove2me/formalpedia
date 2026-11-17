-- Prove2me | Theorems.Thm_Kyprianou_Ch07_ruinProbabilityRegularlyVarying
-- name    : Kyprianou.Ch07.ruinProbabilityRegularlyVarying
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T21:23:11.65935+00:00
-- url     : https://prove2.me/theorems/d169c719-1e1a-4f89-a269-236b3da1f113
-- title:
--   Theorem 7.16(i): ruin probability regularly varying with index minus alpha
-- statement:
--   Prove regular variation of the ruin probability with index -alpha, using Karamata integration of a jump tail with index -(alpha+1) and the integrated-tail asymptotic.
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

theorem Kyprianou.Ch07.ruinProbabilityRegularlyVarying
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
    Kyprianou.Ch05.RegularlyVaryingAtInfinity
       (fun x : Real => (P (ruin x)).toReal) (-alpha) := by
  sorry
