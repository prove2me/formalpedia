-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_isLocallyConstant_splitOm
-- name    : GlobalTheory.WeilM.isLocallyConstant_splitOm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:55:22.077483+00:00
-- url     : https://prove2.me/theorems/3162e6e9-bbd2-4ae4-b18d-6a75cf318d21
-- title:
--   Weil M: is Locally Constant split Om
-- statement:
--   The Weil M construction uses the is Locally Constant split Om property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsLocallyConstantSplitOm.lean#L71-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsLocallyConstantSplitOm.lean#L71-L98

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
omit [DecidableEq α] [Fintype κ]

theorem GlobalTheory.WeilM.isLocallyConstant_splitOm (χ : (F × F)ˣ →* Circle) (hχ : Continuous χ) (J : Matrix β β (F × F)) (σ : κ ≃ α × β)
    {φ : (κ → F) → ℂ} (hφ : φ ∈ SB (κ → F)) : IsLocallyConstant fun h => splitOm (distribHaarChar F) χ J σ h φ := by sorry
