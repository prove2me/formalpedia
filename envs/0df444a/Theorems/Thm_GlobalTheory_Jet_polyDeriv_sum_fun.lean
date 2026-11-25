-- Prove2me | Theorems.Thm_GlobalTheory_Jet_polyDeriv_sum_fun
-- name    : GlobalTheory.Jet.polyDeriv_sum_fun
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:11:50.284413+00:00
-- url     : https://prove2.me/theorems/759984fe-c961-41e8-81b6-9c559a64daf6
-- title:
--   Jet: poly Deriv sum fun
-- statement:
--   The Jet construction uses the poly Deriv sum fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardToMultisetEqDegree.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardToMultisetEqDegree.lean#L52-L56

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open GlobalTheory.Jet
variable {σ W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup W'] [NormedSpace ℂ W']

theorem GlobalTheory.Jet.polyDeriv_sum_fun [FiniteDimensional ℂ W] {κ : Type*} (P : MvPolynomial σ ℂ) (u : σ → W)
    (s : Finset κ) (c : κ → ℂ) (F : κ → W → ℂ) (hF : ∀ i ∈ s, Differentiable ℂ (F i)) (x : W) :
    polyDeriv P u (fun w => ∑ i ∈ s, c i * F i w) x = ∑ i ∈ s, c i * polyDeriv P u (F i) x := by sorry
