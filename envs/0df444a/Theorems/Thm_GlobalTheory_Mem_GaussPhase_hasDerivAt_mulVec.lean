-- Prove2me | Theorems.Thm_GlobalTheory_Mem_GaussPhase_hasDerivAt_mulVec
-- name    : GlobalTheory.Mem.GaussPhase.hasDerivAt_mulVec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:23:14.160782+00:00
-- url     : https://prove2.me/theorems/e6d9e8d3-5c3e-4f95-8246-4ed2e2375237
-- title:
--   Gauss Phase: has Deriv At mul Vec
-- statement:
--   The Gauss Phase construction uses the has Deriv At mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DifferentiableAtInvApply.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DifferentiableAtInvApply.lean#L45-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtInvApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.GaussPhase
variable {σ : Type} [Fintype σ] [DecidableEq σ]
omit [DecidableEq σ]

theorem GlobalTheory.Mem.GaussPhase.hasDerivAt_mulVec (S : Matrix σ σ ℂ) {w : ℝ → σ → ℂ} {w' : σ → ℂ} {t : ℝ}
    (h : HasDerivAt w w' t) : HasDerivAt (fun s => S *ᵥ w s) (S *ᵥ w') t := by sorry
