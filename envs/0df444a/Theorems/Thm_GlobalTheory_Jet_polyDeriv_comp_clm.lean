-- Prove2me | Theorems.Thm_GlobalTheory_Jet_polyDeriv_comp_clm
-- name    : GlobalTheory.Jet.polyDeriv_comp_clm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:39:27.155063+00:00
-- url     : https://prove2.me/theorems/e647f04c-a597-42f0-9d0b-75d2feb3dcc7
-- title:
--   Jet: poly Deriv comp clm
-- statement:
--   The Jet construction uses the poly Deriv comp clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardToMultisetEqDegree.lean#L68-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardToMultisetEqDegree.lean#L68-L74

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

theorem GlobalTheory.Jet.polyDeriv_comp_clm [FiniteDimensional ℂ W'] (P : MvPolynomial σ ℂ) (u : σ → W)
    {F : W' → ℂ} (hF : Differentiable ℂ F) (φ : W →L[ℂ] W') (x : W) :
    polyDeriv P u (F ∘ φ) x = polyDeriv P (φ ∘ u) F (φ x) := by sorry
