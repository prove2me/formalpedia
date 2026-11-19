-- Prove2me | Theorems.Thm_LevyStochCalc_Martingale_martingale_sq_sub_of_setIntegral
-- name    : LevyStochCalc.Martingale.martingale_sq_sub_of_setIntegral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T22:18:11.780609+00:00
-- url     : https://prove2.me/theorems/322f8150-fc97-4382-b52d-c6c5b3c874ca
-- title:
--   martingale sq sub of setIntegral
-- statement:
--   The source theorem `LevyStochCalc.Martingale.martingale_sq_sub_of_setIntegral` is extracted from `LevyStochCalc.Martingale.SquareCompensator`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Martingale_SquareCompensator_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated square of a square-integrable martingale

For a square-integrable martingale `M` and an adapted integrable process `A`, the process
`M² − A` is a martingale as soon as the increments satisfy the set-level identity
`∫_B (M_t − M_s)² = ∫_B (A_t − A_s)` for every `s ≤ t` and every `B ∈ ℱ_s`: the cross term
`∫_B M_s M_t` equals `∫_B M_s²` by the martingale property, so the identity says exactly that
`∫_B (M_t² − A_t) = ∫_B (M_s² − A_s)`.
-/

open MeasureTheory Filter

namespace LevyStochCalc.Martingale

variable {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} {ℱ : Filtration ι mΩ}
  {μ : Measure Ω} [IsFiniteMeasure μ] {M A : ι → Ω → ℝ}

theorem _root_.LevyStochCalc.Martingale.martingale_sq_sub_of_setIntegral (hM : Martingale M ℱ μ) (hM2 : ∀ t, MemLp (M t) 2 μ)
    (hA : StronglyAdapted ℱ A) (hAint : ∀ t, Integrable (A t) μ)
    (h : ∀ s t, s ≤ t → ∀ B, MeasurableSet[ℱ s] B →
      ∫ ω in B, (M t ω - M s ω) ^ 2 ∂μ = ∫ ω in B, (A t ω - A s ω) ∂μ) :
    Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ := by sorry
