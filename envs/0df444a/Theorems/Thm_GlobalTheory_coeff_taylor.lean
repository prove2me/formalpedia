-- Prove2me | Theorems.Thm_GlobalTheory_coeff_taylor
-- name    : GlobalTheory.coeff_taylor
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:49:38.42626+00:00
-- url     : https://prove2.me/theorems/b9cc3152-b1d3-5a4f-bc3a-0986eaaa7927
-- title:
--   Global Theory: coeff taylor
-- statement:
--   The Global Theory construction uses the coeff taylor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L370-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L370-L373

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

theorem GlobalTheory.coeff_taylor (f : (σ → ℂ) → ℂ) (m : σ →₀ ℕ) :
    MvPowerSeries.coeff m (taylor f) = ((∏ i, (m i).factorial : ℕ) : ℂ)⁻¹ *
      ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.monomial m 1)
        (fun i => (Pi.single i 1 : σ → ℂ)) f 0 := by sorry
