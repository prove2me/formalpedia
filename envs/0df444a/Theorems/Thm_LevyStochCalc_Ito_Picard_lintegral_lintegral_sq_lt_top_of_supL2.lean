-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_lintegral_lintegral_sq_lt_top_of_supL2
-- name    : LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_lt_top_of_supL2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:28:39.101189+00:00
-- url     : https://prove2.me/theorems/327dd87f-c989-4d8e-aecd-04335bc28b63
-- title:
--   lintegral lintegral sq lt top of supL2
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_lt_top_of_supL2` is extracted from `LevyStochCalc.Ito.PicardWindow`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardLocality_F000
import Definitions.Def_LevyStochCalc_Ito_PicardLocality_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Solutions of the SDE on a window

`SolvesOn` records that a path map satisfies the jump-diffusion integral equation at every time
of `[0, T]`, in the `picardStep` form; the integrand hypotheses that make the two stochastic
integrals well-typed are bundled existentially, as in
`LevyStochCalc.Ito.Setting.JumpDiffusion.is_solution`, so that a solution can be re-read with any
proof of them. Two solutions on a common window and a common filtration agree, by the Bielecki
contraction.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### From an `S²` bound to the time-integrated energy -/

theorem _root_.LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_lt_top_of_supL2 {Z : ℝ → Ω → (Fin n → ℝ)}
    (hS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (b : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by sorry
