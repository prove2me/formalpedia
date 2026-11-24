-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_isUSplitting_splitOm
-- name    : GlobalTheory.WeilM.isUSplitting_splitOm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:55:32.685798+00:00
-- url     : https://prove2.me/theorems/b5f8a939-38e9-4886-b65d-13737a9d74c7
-- title:
--   Weil M: is USplitting split Om
-- statement:
--   The Weil M construction uses the is USplitting split Om property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsLocallyConstantSplitOm.lean#L145-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsLocallyConstantSplitOm.lean#L145-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsLocallyConstantSplitOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel Filter
open scoped NNReal Topology Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
variable [Invertible (2 : F)] {JA : Matrix α α (F × F)} {JB : Matrix β β (F × F)}

theorem GlobalTheory.WeilM.isUSplitting_splitOm (ψ : AddChar F ℂ) (hA : IsHerm (swapA F) JA) (hB : IsHerm (swapA F) JB) (σ : κ ≃ α × β)
    (χ : (F × F)ˣ →* Circle) (hχ : Continuous χ) :
    IsUSplitting (sbClass F) ψ (splitDarboux hA hB σ) (actB (swapA F)) (splitOm (distribHaarChar F) χ JB σ) := by sorry
