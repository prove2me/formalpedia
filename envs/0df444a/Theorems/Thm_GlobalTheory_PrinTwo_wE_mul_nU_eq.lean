-- Prove2me | Theorems.Thm_GlobalTheory_PrinTwo_wE_mul_nU_eq
-- name    : GlobalTheory.PrinTwo.wE_mul_nU_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:55:16.152151+00:00
-- url     : https://prove2.me/theorems/6c53d7e3-f60d-4021-b8af-bfb63ef25115
-- title:
--   Prin Two: w E mul n U eq
-- statement:
--   The Prin Two construction uses the w E mul n U eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L50-L52

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

theorem GlobalTheory.PrinTwo.wE_mul_nU_eq (x : kˣ) :
    (wE : GL (Fin (1 + 1)) k) * nU (x : k) = bor (-x⁻¹) x 1 * nL ((x⁻¹ : kˣ) : k) := by sorry
