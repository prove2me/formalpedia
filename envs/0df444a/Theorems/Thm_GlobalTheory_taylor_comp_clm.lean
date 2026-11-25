-- Prove2me | Theorems.Thm_GlobalTheory_taylor_comp_clm
-- name    : GlobalTheory.taylor_comp_clm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:43:28.922171+00:00
-- url     : https://prove2.me/theorems/cd732912-1283-443c-845b-b8c141497e01
-- title:
--   Global Theory: taylor comp clm
-- statement:
--   The Global Theory construction uses the taylor comp clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L448-L450
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L448-L450

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
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem GlobalTheory.taylor_comp_clm (L : (σ → ℂ) →L[ℂ] W) {F : W → ℂ} (hF : AnalyticAt ℂ F 0) :
    taylor (fun z => F (L z)) = taylorDir (fun i => L (Pi.single i 1)) F := by sorry
