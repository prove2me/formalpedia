-- Prove2me | Theorems.Thm_GlobalTheory_dirPolyDeriv_eq_sum_coeff_taylor
-- name    : GlobalTheory.dirPolyDeriv_eq_sum_coeff_taylor
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:45:53.036389+00:00
-- url     : https://prove2.me/theorems/e7f58871-2e7b-49a3-bbf0-2579c6264bea
-- title:
--   Global Theory: dir Poly Deriv eq sum coeff taylor
-- statement:
--   The Global Theory construction uses the dir Poly Deriv eq sum coeff taylor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L375-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L375-L378

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
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {f g : (σ → ℂ) → ℂ}

theorem GlobalTheory.dirPolyDeriv_eq_sum_coeff_taylor (P : MvPolynomial σ ℂ) (f : (σ → ℂ) → ℂ) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (fun i => (Pi.single i 1 : σ → ℂ)) f 0 = ∑ m ∈ P.support,
      P.coeff m * ((∏ i, (m i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff m (taylor f) := by sorry
