-- Prove2me | Theorems.Thm_GlobalTheory_Ker_CreOp_holD_mul
-- name    : GlobalTheory.Ker.CreOp.holD_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:48:09.648001+00:00
-- url     : https://prove2.me/theorems/4ad38997-3620-4e72-b3af-ca5410531733
-- title:
--   Cre Op: hol D mul
-- statement:
--   The Cre Op construction uses the hol D mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FoldrHolDEqIteratedFDeriv.lean#L43-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FoldrHolDEqIteratedFDeriv.lean#L43-L51

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

theorem GlobalTheory.Ker.CreOp.holD_mul (T : W →L[ℝ] ℂ) (h2 : ∀ a, T (I • a) = -I * T a) {Φ : W → ℂ}
    (h : Differentiable ℝ Φ) (v : W) :
    holD v (fun z => T z * Φ z) = fun z => T z * holD v Φ z := by sorry
