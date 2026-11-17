-- Prove2me | Theorems.Thm_Kyprianou_Ch07_heavyTailRuinAsymptoticAllParts
-- name    : Kyprianou.Ch07.heavyTailRuinAsymptoticAllParts
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T14:54:59.764577+00:00
-- url     : https://prove2.me/theorems/356dccb0-7890-47ae-8c8c-17297f2edcfa
-- title:
--   Theorem 7.16: heavy-tail ruin probability and conditional joint deficit limit
-- statement:
--   For a spectrally positive Lévy process X with negative finite mean E X₁, and a positive-jump Lévy-measure tail Π(x,∞) regularly varying with index −(α+1) for α>0: (i) P(τ⁺_x<∞)∼[1/|E X₁|]∫_x^∞ Π(u,∞)du, and the ruin probability itself is regularly varying with index −α. (ii) For all u,v>0 the conditional probability, given ruin, of the normalised overshoot (X_{τ⁺_x}−x)/(x/α)>u and the normalised negative pre-ruin position (−X_{τ⁺_x−})/(x/α)>v tends to (1+(u+v)/α)^(−α). The distinct pre-jump left limit is explicitly required, with genuine finite first passage.
-- source:
--   Kyprianou (2006), Theorem 7.16(i)–(ii), printed p.204, original single-page PDF p.213, Windows Ky.pdf landscape sheet 107.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Theorem 7.16(i)-(ii): regularly varying ruin probability and
the bivariate generalised Pareto law of overshoot and pre-ruin position. -/
theorem heavyTailRuinAsymptoticAllParts
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
    ((Tendsto (fun x : Real =>
       (P (ruin x)).toReal / integratedTail x)
       atTop (nhds (1 / |∫ omega, X 1 omega ∂P|))) ∧
     Kyprianou.Ch05.RegularlyVaryingAtInfinity
       (fun x : Real => (P (ruin x)).toReal) (-alpha) ∧
     (∀ u v : Real, 0 < u → 0 < v →
       Tendsto (fun x : Real =>
         (P {omega | omega ∈ ruin x ∧
             u < overshoot x omega / (x / alpha) ∧
             v < (-prejump x omega) / (x / alpha)}).toReal /
           (P (ruin x)).toReal)
         atTop (nhds ((1 + (u + v) / alpha) ^ (-alpha))))) := by
  sorry

end Kyprianou.Ch07
