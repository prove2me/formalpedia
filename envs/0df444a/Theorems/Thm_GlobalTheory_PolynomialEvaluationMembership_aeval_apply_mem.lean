-- Prove2me | Theorems.Thm_GlobalTheory_PolynomialEvaluationMembership_aeval_apply_mem
-- name    : GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:49:34.554106+00:00
-- url     : https://prove2.me/theorems/09c18cc4-163f-4386-b57b-6dc892df49f8
-- title:
--   Polynomial Evaluation Membership: aeval apply mem
-- statement:
--   The Polynomial Evaluation Membership construction uses the aeval apply mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AevalApplyMem.lean#L15-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AevalApplyMem.lean#L15-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AevalApplyMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PolynomialEvaluationMembership

theorem GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (g : Module.End F V) (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (p : Polynomial F) :
    ∀ x ∈ W, (Polynomial.aeval g p) x ∈ W := by sorry
