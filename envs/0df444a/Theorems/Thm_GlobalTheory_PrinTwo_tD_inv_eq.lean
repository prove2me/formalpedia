-- Prove2me | Theorems.Thm_GlobalTheory_PrinTwo_tD_inv_eq
-- name    : GlobalTheory.PrinTwo.tD_inv_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:16:35.1216+00:00
-- url     : https://prove2.me/theorems/0f67d4a9-d600-45e4-a39e-373c4172bf9c
-- title:
--   Prin Two: t D inv eq
-- statement:
--   The Prin Two construction uses the t D inv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L58-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.PrinTwo
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.PrinTwo.tD_inv_eq (a : kˣ) : (tD a a⁻¹ : GL (Fin (1 + 1)) k) =
    nU (a : k) * nL (-((a⁻¹ : kˣ) : k)) * nU (a : k) * (nU (-1) * nL 1 * nU (-1)) := by sorry
