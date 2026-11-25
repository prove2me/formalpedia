-- Prove2me | Theorems.Thm_Kyprianou_Ch04_rawCompensationClockRegularity
-- name    : Kyprianou.Ch04.rawCompensationClockRegularity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T10:22:15.175729+00:00
-- url     : https://prove2.me/theorems/772315ef-b0e6-490d-9ac6-2a224f295f0c
-- title:
--   Raw nonnegative Poisson clock measurability and real conversion
-- statement:
--   Use the past count evaluations and finite bands to obtain adapted extended clock measurability. The real integral is its toReal pointwise by nonnegativity.
-- source:
--   Kyprianou (2006), corrected Corollary 4.6.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
open Kyprianou.Ch04

theorem Kyprianou.Ch04.rawCompensationClockRegularity
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (phi : Real → Real → Omega → Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (t : NNReal)
    (hKernelPast : Measurable[(F t).prod inferInstance]
      (fun z : Omega × (Real × Real) =>
        if z.2.1 ∈ Set.Icc (0 : Real) (t : Real) then phi z.2.1 z.2.2 z.1 else 0))
    (N : PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hPast : ∀ B : Set (Real × Real), MeasurableSet B →
      B ⊆ Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ →
      Measurable[F t] (fun w => N.N w B))
    (hLocalFinite : ∀ n : Nat, ∀ w : Omega,
      N.N w (Set.Icc (0 : Real) (t : Real) ×ˢ spanningSets levyMeasure n) ≠ ⊤) :
    Measurable[F t] (fun w => ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
      ENNReal.ofReal (phi z.1 z.2 w) ∂(N.N w)) ∧
    StronglyMeasurable[F t] (fun w => ∫ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
      phi z.1 z.2 w ∂(N.N w)) ∧
    (∀ w, (∫ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
      phi z.1 z.2 w ∂(N.N w)) =
      (∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
        ENNReal.ofReal (phi z.1 z.2 w) ∂(N.N w)).toReal) := by
  sorry
