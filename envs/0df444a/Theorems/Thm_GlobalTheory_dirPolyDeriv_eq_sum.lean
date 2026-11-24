-- Prove2me | Theorems.Thm_GlobalTheory_dirPolyDeriv_eq_sum
-- name    : GlobalTheory.dirPolyDeriv_eq_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:43:31.668872+00:00
-- url     : https://prove2.me/theorems/970975eb-fc74-474b-adad-4efa5a295051
-- title:
--   Global Theory: dir Poly Deriv eq sum
-- statement:
--   The Global Theory construction uses the dir Poly Deriv eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L65-L69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem GlobalTheory.dirPolyDeriv_eq_sum (P : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) (x : W) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u F x = ∑ m ∈ P.support,
      P.coeff m * ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.monomial m 1) u F x := by sorry
