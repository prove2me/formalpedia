-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_ae_eq_zero_of_perpItoIntegrals_augFiltration
-- name    : LevyStochCalc.Brownian.Ito.ae_eq_zero_of_perpItoIntegrals_augFiltration
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:47:42.703578+00:00
-- url     : https://prove2.me/theorems/2160bc5b-db78-4d81-a82e-44494087a614
-- title:
--   ae eq zero of perpItoIntegrals augFiltration
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.ae_eq_zero_of_perpItoIntegrals_augFiltration` is extracted from `LevyStochCalc.Brownian.PRPBrownian`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_isBrownianFiltration_natural
import Definitions.Def_LevyStochCalc_Brownian_PRPBrownian_F000
import Definitions.Def_SourceProof_947c94e08f8784ad6039b2d1

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The orthogonal complement of the Brownian Itô integrals

Sorting the times of a finite family of coordinate values into an increasing grid turns a
cylinder character of a multidimensional Brownian motion into a character of the values along a
grid, so a square-integrable weight of mean zero orthogonal to every coordinate's Itô integrals
is orthogonal to every cylinder character. A weight measurable for the natural filtration at a
time `T` is therefore almost everywhere zero.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

theorem _root_.LevyStochCalc.Brownian.Ito.ae_eq_zero_of_perpItoIntegrals_augFiltration (W : Multidim.MultidimBrownianMotion P d)
    {Z : Ω → ℂ} (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) (augFiltration W.naturalFiltration P)
      (isBrownianFiltration_augFiltration (W.isBrownianFiltration_natural i)) Z)
    (hZ0 : ∫ ω, Z ω ∂P = 0) {T : ℝ} (hT : 0 ≤ T)
    (hZT : StronglyMeasurable[augFiltration W.naturalFiltration P T] Z) :
    Z =ᵐ[P] 0 := by sorry
