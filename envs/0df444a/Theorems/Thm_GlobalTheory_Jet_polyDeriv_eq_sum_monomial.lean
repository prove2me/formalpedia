-- Prove2me | Theorems.Thm_GlobalTheory_Jet_polyDeriv_eq_sum_monomial
-- name    : GlobalTheory.Jet.polyDeriv_eq_sum_monomial
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:39:32.947098+00:00
-- url     : https://prove2.me/theorems/9f078364-c91d-4e32-a449-1b83bfd2455a
-- title:
--   Jet: poly Deriv eq sum monomial
-- statement:
--   The Jet construction uses the poly Deriv eq sum monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardToMultisetEqDegree.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CardToMultisetEqDegree.lean#L25-L29

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

theorem GlobalTheory.Jet.polyDeriv_eq_sum_monomial (P : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) (x : W) :
    polyDeriv P u F x =
      ∑ m ∈ P.support, P.coeff m * polyDeriv (MvPolynomial.monomial m (1 : ℂ)) u F x := by sorry
