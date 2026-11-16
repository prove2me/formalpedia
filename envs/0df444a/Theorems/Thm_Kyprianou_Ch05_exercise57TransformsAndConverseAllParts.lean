-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise57TransformsAndConverseAllParts
-- name    : Kyprianou.Ch05.exercise57TransformsAndConverseAllParts
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:58:57.621229+00:00
-- url     : https://prove2.me/theorems/567054ee-3ffb-4790-af05-1b167a987cca
-- title:
--   Exercise 5.7: integrated transforms, scaling, endpoint limits and converse
-- statement:
--   All four parts: exact jump-only double Laplace identity with q>gamma; rescaled joint transform including creeping; degenerate RV index 0 and 1 behaviours at both endpoints; converse necessity of interior-index regular variation given a non-atomic weak limit.
-- source:
--   Kyprianou (2006), first edition, Exercise 5.7, pp.135-137 and author worked solution pp.324-327.

import Definitions.Def_Kyprianou_Ch05_ExponentialPassageMoments
import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Exercise 5.7, all four parts: complete transform and creeping,
rescaling, trivial endpoints and converse regular variation. -/
theorem exercise57TransformsAndConverseAllParts
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (U : Real → Measure Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hLeft : IsLeftLimitVersion P Y Yleft)
 :
  -- (i) Jump-only integrated joint transform, q>gamma.
  ((∀ beta gamma q : Real, 0 ≤ beta → 0 ≤ gamma → gamma < q →
    (∫ x in Set.Ioi (0 : Real),
       Real.exp (-q*x) *
         jointFirstPassageMoment P Y Yleft death beta gamma x true ∂volume) =
      ((Phi q - Phi gamma) / (Phi (q+beta)) / (q-gamma)) -
        d / Phi (q+beta)) ∧
   -- (ii) Full transform includes creeping and scales t>0.
   (∀ beta gamma q t : Real,
      0 ≤ beta → 0 ≤ gamma → gamma < q → 0 < t →
      (∫ x in Set.Ioi (0 : Real),
        Real.exp (-q*x) *
          jointFirstPassageMoment P Y Yleft death (beta/t) (gamma/t) (t*x)
          false ∂volume) =
        (Phi (q/t) - Phi (gamma/t)) /
          ((q-gamma) * Phi ((q+beta)/t))) ∧
   -- (iii) For alpha=1, levels become asymptotically continuous:
   -- pre-crossing fraction->1 and overshoot fraction->0.
   (∀ atZero : Bool,
      (if atZero then RegularlyVaryingAtZero Phi 1
       else RegularlyVaryingAtInfinity Phi 1) →
      ∀ epsilon : Real, 0 < epsilon →
        Tendsto
          (fun x : Real =>
            (P {omega : Omega |
              PassageFinite Y death x omega ∧
              (|Yleft (passageFiniteTime Y death x omega) omega / x - 1| >
                 epsilon ∨
               passageOvershoot Y death x omega / x > epsilon)}).toReal)
          (if atZero then atTop else nhdsWithin (0 : Real) (Set.Ioi 0))
          (nhds 0)) ∧
   -- alpha=0: pre-crossing fraction vanishes and overshoot/x escapes,
   -- so there is no tight, nondegenerate R^2 limiting law.
   (∀ atZero : Bool,
      (if atZero then RegularlyVaryingAtZero Phi 0
       else RegularlyVaryingAtInfinity Phi 0) →
      (∀ epsilon : Real, 0 < epsilon →
        Tendsto
          (fun x : Real =>
            (P {omega : Omega |
              PassageFinite Y death x omega ∧
              Yleft (passageFiniteTime Y death x omega) omega / x >
                epsilon}).toReal)
          (if atZero then atTop else nhdsWithin (0 : Real) (Set.Ioi 0))
          (nhds 0)) ∧
      (∀ M : Real, 0 < M →
        Tendsto
          (fun x : Real =>
            (P {omega : Omega |
              PassageFinite Y death x omega ∧
              passageOvershoot Y death x omega / x ≤ M}).toReal)
          (if atZero then atTop else nhdsWithin (0 : Real) (Set.Ioi 0))
          (nhds 0))) ∧
   -- (iv) Nondegenerate weak limits imply Phi is regularly varying
   -- at the opposite endpoint with a strictly interior index.
   (∀ atZero : Bool,
     ∀ mu : Measure (Real × Real), IsProbabilityMeasure mu →
       (∀ f : Real × Real → Real, IsBoundedContinuousTest f →
         Tendsto
           (fun x : Real =>
             ∫ omega in {omega : Omega | PassageFinite Y death x omega},
               f (Yleft (passageFiniteTime Y death x omega) omega / x,
                  passageOvershoot Y death x omega / x) ∂P)
           (if atZero then atTop else nhdsWithin (0 : Real) (Set.Ioi 0))
           (nhds (∫ z : Real × Real, f z ∂mu))) →
       -- General necessity, including possible degenerate weak limits.
       (∃ alpha : Real,
          0 ≤ alpha ∧ alpha ≤ 1 ∧
          (if atZero then RegularlyVaryingAtZero Phi alpha
           else RegularlyVaryingAtInfinity Phi alpha)) ∧
       -- A non-Dirac limit forces a strictly interior index.
       ((¬∃ z : Real × Real, mu = Measure.dirac z) →
         ∃ alpha : Real,
           0 < alpha ∧ alpha < 1 ∧
           (if atZero then RegularlyVaryingAtZero Phi alpha
            else RegularlyVaryingAtInfinity Phi alpha)))) ∧
  -- Sufficiency in the printed 'if and only if': an interior index gives
  -- a non-Dirac probability weak limit of the scaled passage pair.
  (∀ atZero : Bool, ∀ alpha : Real,
     0 < alpha → alpha < 1 →
     (if atZero then RegularlyVaryingAtZero Phi alpha
      else RegularlyVaryingAtInfinity Phi alpha) →
     ∃ mu : Measure (Real × Real),
       IsProbabilityMeasure mu ∧
       (¬∃ z : Real × Real, mu = Measure.dirac z) ∧
       (∀ f : Real × Real → Real, IsBoundedContinuousTest f →
         Tendsto
           (fun x : Real =>
             ∫ omega in {omega : Omega | PassageFinite Y death x omega},
               f (Yleft (passageFiniteTime Y death x omega) omega / x,
                  passageOvershoot Y death x omega / x) ∂P)
           (if atZero then atTop else nhdsWithin (0 : Real) (Set.Ioi 0))
           (nhds (∫ z : Real × Real, f z ∂mu))))
 := by
  sorry

end Kyprianou.Ch05
