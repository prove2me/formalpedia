-- Prove2me | Theorems.Thm_GlobalTheory_ThetaFamily_differentiableOn_left_inverse
-- name    : GlobalTheory.ThetaFamily.differentiableOn_left_inverse
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:05:19.104904+00:00
-- url     : https://prove2.me/theorems/2fdfca90-5046-4707-b0bc-ccdb6ca03837
-- title:
--   Theta Family: differentiable On left inverse
-- statement:
--   The Theta Family construction uses the differentiable On left inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfFiniteOfClosedFibres.lean#L119-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfFiniteOfClosedFibres.lean#L119-L133

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DifferentiableOnQuotientOfDifferentiableOnSlice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfFiniteOfClosedFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Metric Set
open scoped Topology
open GlobalTheory GlobalTheory.ThetaFamily

theorem GlobalTheory.ThetaFamily.differentiableOn_left_inverse {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : Type} [Fintype n]
    [DecidableEq n] {B : Set V} {M h : V → Matrix n n ℂ} (hM : ∀ i j, DifferentiableOn ℂ (fun b => M b i j) B)
    (hh : ∀ b ∈ B, h b * M b = 1) (i j : n) : DifferentiableOn ℂ (fun b => h b i j) B := by sorry
