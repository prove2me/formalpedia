-- Prove2me | Theorems.Thm_Kyprianou_Ch05_classicalRenewalTheorem_keyRenewalConvolutionV2
-- name    : Kyprianou.Ch05.classicalRenewalTheorem_keyRenewalConvolutionV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T18:24:37.296375+00:00
-- url     : https://prove2.me/theorems/4cd63d57-c64f-46ba-8ed9-fa0c7d76a0b1
-- title:
--   Theorem 5.1(ii) corrected: measurable directly Riemann integrable key renewal theorem
-- statement:
--   Theorem 5.1(ii) corrected: measurable directly Riemann integrable key renewal theorem
-- source:
--   Kyprianou (2006), Theorem 5.1, corrected Borel-measurable key renewal theorem; discussion 1dbfd76f-095f-4acc-b3fe-3e528b888bc6.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.classicalRenewalTheorem_keyRenewalConvolutionV2
    (F : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hFiniteMean : Integrable (fun x : Real => x) F)
    (hPositiveMean : 0 < ∫ x : Real, x ∂F) :
    let mu := ∫ x : Real, x ∂F
    let V := renewalMeasure F
    (NonLatticeMeasure F → ∀ h : Real → Real,
      Measurable h → DirectlyRiemannIntegrable h →
      Tendsto (fun x : Real => ∫ z in Set.Icc 0 x, h (x-z) ∂V)
        atTop (nhds ((∫ z in Set.Ici 0, h z ∂volume) / mu))) := by sorry
