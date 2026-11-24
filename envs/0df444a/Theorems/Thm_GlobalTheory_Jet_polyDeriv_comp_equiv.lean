-- Prove2me | Theorems.Thm_GlobalTheory_Jet_polyDeriv_comp_equiv
-- name    : GlobalTheory.Jet.polyDeriv_comp_equiv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:39:34.868971+00:00
-- url     : https://prove2.me/theorems/5fab4d8b-67c8-40f6-9f0e-9a37329181ac
-- title:
--   Jet: poly Deriv comp equiv
-- statement:
--   The Jet construction uses the poly Deriv comp equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardToMultisetEqDegree.lean#L58-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardToMultisetEqDegree.lean#L58-L66

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

theorem GlobalTheory.Jet.polyDeriv_comp_equiv (P : MvPolynomial σ ℂ) (u : σ → W) (F : W' → ℂ) (φ : W ≃L[ℂ] W')
    (x : W) : polyDeriv P u (F ∘ φ) x = polyDeriv P (φ ∘ u) F (φ x) := by sorry
