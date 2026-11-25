-- Prove2me | Theorems.Thm_GlobalTheory_Jet_polyDeriv_smul_fun
-- name    : GlobalTheory.Jet.polyDeriv_smul_fun
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:11:37.291112+00:00
-- url     : https://prove2.me/theorems/e75c759c-1520-473c-b968-fdcc4bbabc45
-- title:
--   Jet: poly Deriv smul fun
-- statement:
--   The Jet construction uses the poly Deriv smul fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardToMultisetEqDegree.lean#L42-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardToMultisetEqDegree.lean#L42-L50

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

theorem GlobalTheory.Jet.polyDeriv_smul_fun [FiniteDimensional ℂ W] (P : MvPolynomial σ ℂ) (u : σ → W)
    {F : W → ℂ} (hF : Differentiable ℂ F) (c : ℂ) (x : W) :
    polyDeriv P u (c • F) x = c * polyDeriv P u F x := by sorry
