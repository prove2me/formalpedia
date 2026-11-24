-- Prove2me | Theorems.Thm_GlobalTheory_Ker_CreOp_holD_of_differentiableAt
-- name    : GlobalTheory.Ker.CreOp.holD_of_differentiableAt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:48:04.969149+00:00
-- url     : https://prove2.me/theorems/592dad29-4bff-4d27-be7d-c7b48ed8fec7
-- title:
--   Cre Op: hol D of differentiable At
-- statement:
--   The Cre Op construction uses the hol D of differentiable At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FoldrHolDEqIteratedFDeriv.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FoldrHolDEqIteratedFDeriv.lean#L53-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FoldrHolDEqIteratedFDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.Ker GlobalTheory.Ker.CreOp
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem GlobalTheory.Ker.CreOp.holD_of_differentiableAt {Φ : W → ℂ} {z : W} (h : DifferentiableAt ℂ Φ z) (v : W) :
    holD v Φ z = fderiv ℂ Φ z v := by sorry
