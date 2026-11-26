-- Prove2me | Theorems.Thm_Kyprianou_Ch04_boundedSupportedPhysicalPastMeasurableV1
-- name    : Kyprianou.Ch04.boundedSupportedPhysicalPastMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:26:02.847326+00:00
-- url     : https://prove2.me/theorems/016a3a28-a89f-5a0b-ab25-b249cdc59ec5
-- title:
--   Past measurability of bounded supported predictable physical integrals
-- statement:
--   A bounded predictable physical integral over a finite mark band is measurable in the completed natural past, using a pointwise finite measurable version and time clamping.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem boundedSupportedPhysicalPastMeasurableV1 {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (X : NNReal → Ω → ℝ) (F : Filtration NNReal mΩ)
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (R : Ω → Measure (ℝ × ℝ)) (T : NNReal) (B : Set ℝ)
    (hB : MeasurableSet B)
    (hPast : ∀ S : Set (ℝ × ℝ), MeasurableSet S →
      S ⊆ Icc (0 : ℝ) (T : ℝ) ×ˢ B → Measurable[F T] (fun w => R w S))
    (hFin : ∀ᵐ w ∂P, R w (Icc (0 : ℝ) (T : ℝ) ×ˢ B) < ⊤)
    (g : (NNReal × Ω) × ℝ → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g)
    (C : ℝ) (hC : ∀ p, ‖g p‖ ≤ C) (hs : ∀ p, p.2 ∉ B → g p = 0) :
    Measurable[F T] (fun w => ∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ univ,
      g ((z.1.toNNReal,w),z.2) ∂(R w)) := by
  sorry
end Kyprianou.Ch04
