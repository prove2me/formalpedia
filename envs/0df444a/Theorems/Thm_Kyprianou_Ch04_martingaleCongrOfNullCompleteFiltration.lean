-- Prove2me | Theorems.Thm_Kyprianou_Ch04_martingaleCongrOfNullCompleteFiltration
-- name    : Kyprianou.Ch04.martingaleCongrOfNullCompleteFiltration
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:41:07.276803+00:00
-- url     : https://prove2.me/theorems/b8186cef-53bb-4128-babd-0a5f618405e1
-- title:
--   martingaleCongrOfNullCompleteFiltration
-- statement:
--   A real martingale remains a martingale under an almost sure modification at each time in a null-complete filtration.
-- source:
--   Kyprianou (2006), Exercise 4.3(ii).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- In a null-complete filtration, an arbitrary modification of a real martingale is a martingale. -/
theorem Kyprianou.Ch04.martingaleCongrOfNullCompleteFiltration {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hNull : ∀ (s : NNReal) (N A : Set Omega), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (M Y : NNReal → Omega → ℝ) (hM : Martingale M F P)
    (he : ∀ t, M t =ᵐ[P] Y t) : Martingale Y F P := by
  sorry
