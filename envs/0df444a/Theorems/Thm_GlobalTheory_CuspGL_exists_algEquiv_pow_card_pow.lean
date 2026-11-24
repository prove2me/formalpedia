-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_exists_algEquiv_pow_card_pow
-- name    : GlobalTheory.CuspGL.exists_algEquiv_pow_card_pow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:31:08.42284+00:00
-- url     : https://prove2.me/theorems/c4abbfd3-36dd-4c47-b0ad-3335279e6b09
-- title:
--   Cusp GL: exists alg Equiv pow card pow
-- statement:
--   The Cusp GL construction uses the exists alg Equiv pow card pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InnerProductRootPowerSumEqOfFrobeniusModEq.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InnerProductRootPowerSumEqOfFrobeniusModEq.lean#L10-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndInnerProductRootPowerSumEqTorusSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InnerProductRootPowerSumEqOfFrobeniusModEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.exists_algEquiv_pow_card_pow (F : Type) [Field F] [Finite F] (i : ℕ) :
    ∃ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, ∀ α, σ α = α ^ (Nat.card F ^ i) := by sorry
