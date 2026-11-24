-- Prove2me | Theorems.Thm_GlobalTheory_Ker_CreOp_contDiff_foldr_holD
-- name    : GlobalTheory.Ker.CreOp.contDiff_foldr_holD
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:48:09.234269+00:00
-- url     : https://prove2.me/theorems/43e6befb-2b12-4580-b995-95302760c0aa
-- title:
--   Cre Op: cont Diff foldr hol D
-- statement:
--   The Cre Op construction uses the cont Diff foldr hol D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FoldrHolDEqIteratedFDeriv.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FoldrHolDEqIteratedFDeriv.lean#L62-L66

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
variable {σ : Type} (u : σ → W)

theorem GlobalTheory.Ker.CreOp.contDiff_foldr_holD {Φ : W → ℂ} (h : ContDiff ℝ (⊤ : ℕ∞) Φ) (M : List σ) :
    ContDiff ℝ (⊤ : ℕ∞) (M.foldr (fun l => holD (u l)) Φ) := by sorry
