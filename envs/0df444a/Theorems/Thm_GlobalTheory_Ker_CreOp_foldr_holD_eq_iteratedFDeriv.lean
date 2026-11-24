-- Prove2me | Theorems.Thm_GlobalTheory_Ker_CreOp_foldr_holD_eq_iteratedFDeriv
-- name    : GlobalTheory.Ker.CreOp.foldr_holD_eq_iteratedFDeriv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:48:11.629806+00:00
-- url     : https://prove2.me/theorems/975e0910-f1fe-4057-8e77-cec31562e7ba
-- title:
--   Cre Op: foldr hol D eq iterated FDeriv
-- statement:
--   The Cre Op construction uses the foldr hol D eq iterated FDeriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FoldrHolDEqIteratedFDeriv.lean#L68-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FoldrHolDEqIteratedFDeriv.lean#L68-L82

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

theorem GlobalTheory.Ker.CreOp.foldr_holD_eq_iteratedFDeriv [FiniteDimensional ℂ W] {θ : W → ℂ}
    (hθ : Differentiable ℂ θ) (M : List σ) :
    M.foldr (fun l => holD (u l)) θ =
      fun z => iteratedFDeriv ℂ M.length θ z fun k => u (M.get k) := by sorry
