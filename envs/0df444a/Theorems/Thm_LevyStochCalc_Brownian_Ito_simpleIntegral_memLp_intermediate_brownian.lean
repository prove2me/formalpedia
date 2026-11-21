-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_simpleIntegral_memLp_intermediate_brownian
-- name    : LevyStochCalc.Brownian.Ito.simpleIntegral_memLp_intermediate_brownian
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T16:47:29.164389+00:00
-- url     : https://prove2.me/theorems/5cb62a64-3417-432d-b0a2-f4f59a001e75
-- title:
--   simpleIntegral memLp intermediate brownian
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.simpleIntegral_memLp_intermediate_brownian` is extracted from `LevyStochCalc.Brownian.ItoL2CompletionIncrement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionExistence_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionExistence_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: increment expansions and the intermediate-time isometry

Diagonal and off-diagonal expectations of products of Brownian increments against
adapted weights, the Bochner expansion of the square of a simple integral clamped
at an intermediate time, and the isometry
`∫⁻ ‖simpleIntegral W H t‖₊² = ∫⁻ ∫⁻_{[0, t]} ‖H.eval‖₊²` it gives for every
intermediate time `t`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.simpleIntegral_memLp_intermediate_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i))
    {t : ℝ} (ht_nn : 0 ≤ t) (htT : t ≤ T) :
    MeasureTheory.MemLp (fun ω => simpleIntegral W H t ω) 2 P := by sorry
