-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittSplit_exists_right_inv_unit
-- name    : GlobalTheory.SgAlg.WittSplit.exists_right_inv_unit
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:54:42.785718+00:00
-- url     : https://prove2.me/theorems/3a1fab8c-c496-4e04-8cf6-77c6f7b33fa7
-- title:
--   Witt Split: exists right inv unit
-- statement:
--   The Witt Split construction uses the exists right inv unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittFreeTuplesSplitQuadraticEtale.lean#L108-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittFreeTuplesSplitQuadraticEtale.lean#L108-L116

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittSplit
variable {F : Type} [Field F] {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]

theorem GlobalTheory.SgAlg.WittSplit.exists_right_inv_unit (φ φ' : Matrix k m F) (hφ : ∃ ψ : Matrix m k F, φ * ψ = 1)
    (hφ' : ∃ ψ : Matrix m k F, φ' * ψ = 1) : ∃ ψ : Matrix m k F, φ' * ψ = 1 ∧ IsUnit (φ * ψ).det := by sorry
