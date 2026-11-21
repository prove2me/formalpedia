-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_perpItoIntegrals_combineBM
-- name    : LevyStochCalc.Brownian.Ito.perpItoIntegrals_combineBM
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:12:57.073121+00:00
-- url     : https://prove2.me/theorems/4db351dc-4edc-4293-886b-75d459148fde
-- title:
--   perpItoIntegrals combineBM
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.perpItoIntegrals_combineBM` is extracted from `LevyStochCalc.Brownian.PRPMultidim`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDriverLinear_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F000
import Definitions.Def_LevyStochCalc_Brownian_PRPGrid_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# One window of the multidimensional Brownian predictable representation

A weight orthogonal to every coordinate's Itô integrals is orthogonal to the integrals against
any unit linear combination of the coordinates, so the one-window statement transfers, and a
multidimensional cell character is a scalar character of the combination.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

theorem _root_.LevyStochCalc.Brownian.Ito.perpItoIntegrals_combineBM (W : Multidim.MultidimBrownianMotion P d) {c : Fin d → ℝ}
    (hc : ∑ i, c i ^ 2 = 1) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱB : IsBrownianFiltration (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    {Z : Ω → ℂ} (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) Z) :
    PerpItoIntegrals (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ hℱB Z := by sorry
