-- Prove2me | Theorems.Thm_GlobalTheory_PosSemidefShiftByScalar_posSemidef_sub_smul_one
-- name    : GlobalTheory.PosSemidefShiftByScalar.posSemidef_sub_smul_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:51:08.980995+00:00
-- url     : https://prove2.me/theorems/781a858b-b343-495c-9820-ec4fa38c3549
-- title:
--   Pos Semidef Shift By Scalar: pos Semidef sub smul one
-- statement:
--   The Pos Semidef Shift By Scalar construction uses the pos Semidef sub smul one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/PosSemidefSubSmulOne.lean#L8-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/PosSemidefSubSmulOne.lean#L8-L28

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubSmulOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Unitary
open scoped ComplexOrder
open GlobalTheory GlobalTheory.PosSemidefShiftByScalar

theorem GlobalTheory.PosSemidefShiftByScalar.posSemidef_sub_smul_one {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ δ' : ℝ, δ' ≤ δ → (A - (δ' : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by sorry
