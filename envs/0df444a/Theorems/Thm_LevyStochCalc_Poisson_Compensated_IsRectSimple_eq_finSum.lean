-- Prove2me | Theorems.Thm_LevyStochCalc_Poisson_Compensated_IsRectSimple_eq_finSum
-- name    : LevyStochCalc.Poisson.Compensated.IsRectSimple.eq_finSum
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T22:41:45.875358+00:00
-- url     : https://prove2.me/theorems/e431bdef-62a0-421f-92a9-cdd2ad53fbc9
-- title:
--   eq finSum
-- statement:
--   The source theorem `LevyStochCalc.Poisson.Compensated.IsRectSimple.eq_finSum` is extracted from `LevyStochCalc.Poisson.CompensatedDensityRectSimple`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRectSimple_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Rectangle-simple functions and their `L²` density

Finite `ℝ`-linear combinations of indicators of measurable rectangles `A ×ˢ B ⊆ Ω × E`, their
closure properties, and their density in `L²(μ)` for a finite measure `μ` on `Ω × E`. The
density is obtained from the monotone-class theorem over the rectangle π-system, so no countable
generation or standard-Borel hypothesis on `E` is required; a trimmed-product lemma transfers
`L²` bounds along a sub-σ-algebra of `Ω`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Mark discretisation via rectangle density (general `E`)

To turn the (mark-continuous) shifted dyadic eval into a genuine `SimplePredictable`,
we approximate the mark dependence by `ℝ`-linear combinations of indicators of
measurable rectangles `A ×ˢ B`. These are dense in `L²(μΩ ⊗ μE)` for *finite*
measures by the monotone-class theorem over the rectangle π-system
(`isPiSystem_prod`/`generateFrom_prod`) — **no countable-generation/standard-Borel
on `E` is needed**. -/

theorem _root_.LevyStochCalc.Poisson.Compensated.IsRectSimple.eq_finSum {g : Ω × E → ℝ} (hg : IsRectSimple g) :
    ∃ (K : ℕ) (a : Fin K → ℝ) (A : Fin K → Set Ω) (B : Fin K → Set E),
      (∀ k, MeasurableSet (A k)) ∧ (∀ k, MeasurableSet (B k)) ∧
      (∀ ω e, g (ω, e) = ∑ k : Fin K, a k * (A k).indicator (fun _ => (1 : ℝ)) ω
                              * (B k).indicator (fun _ => (1 : ℝ)) e) := by sorry
