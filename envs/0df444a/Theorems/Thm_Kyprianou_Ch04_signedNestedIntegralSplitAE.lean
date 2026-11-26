-- Prove2me | Theorems.Thm_Kyprianou_Ch04_signedNestedIntegralSplitAE
-- name    : Kyprianou.Ch04.signedNestedIntegralSplitAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:15:59.659226+00:00
-- url     : https://prove2.me/theorems/f33d2cdc-4f69-5c82-87b4-c717674effd8
-- title:
--   signedNestedIntegralSplitAE
-- statement:
--   Finite expected signed-part compensator masses justify a.e. splitting of the nested signed time-mark integral.
-- source:
--   Kyprianou (2006), Exercise 4.3(ii), pp. 106-107.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Finite expected signed-part compensator masses justify nested subtraction. -/
theorem Kyprianou.Ch04.signedNestedIntegralSplitAE {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (nu : Measure ℝ) [SigmaFinite nu] (t : NNReal)
    (f : Omega → ℝ × ℝ → ℝ)
    (hf : Measurable (fun z : Omega × (ℝ × ℝ) => f z.1 z.2))
    (hp : (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫⁻ x, ENNReal.ofReal (max (f w (s,x)) 0) ∂nu ∂volume ∂P) < ⊤)
    (hn : (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫⁻ x, ENNReal.ofReal (max (-f w (s,x)) 0) ∂nu ∂volume ∂P) < ⊤) :
    ∀ᵐ w ∂P,
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∫ x, f w (s,x) ∂nu ∂volume) =
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∫ x, max (f w (s,x)) 0 ∂nu ∂volume) -
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∫ x, max (-f w (s,x)) 0 ∂nu ∂volume) := by
  sorry
