-- Prove2me | Theorems.Thm_GlobalTheory_Jet_polyDeriv_comp_smul
-- name    : GlobalTheory.Jet.polyDeriv_comp_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:39:40.381048+00:00
-- url     : https://prove2.me/theorems/22a90b1b-69fb-42bc-a2b2-727677c4b1cf
-- title:
--   Jet: poly Deriv comp smul
-- statement:
--   The Jet construction uses the poly Deriv comp smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardToMultisetEqDegree.lean#L95-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardToMultisetEqDegree.lean#L95-L98

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

theorem GlobalTheory.Jet.polyDeriv_comp_smul [FiniteDimensional ℂ W] {P : MvPolynomial σ ℂ} {a : ℕ}
    (hP : P.IsHomogeneous a) (c : ℂ) (u : σ → W) {F : W → ℂ} (hF : Differentiable ℂ F) :
    polyDeriv P u (fun v => F (c • v)) 0 = c ^ a * polyDeriv P u F 0 := by sorry
