-- Prove2me | Theorems.Thm_GlobalTheory_adjoin_hom_extend_of_denominator
-- name    : GlobalTheory.adjoin_hom_extend_of_denominator
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:05:56.995798+00:00
-- url     : https://prove2.me/theorems/a568ca3c-ad3c-4bf5-bc3a-1553f56a6fe3
-- title:
--   Global Theory: adjoin hom extend of denominator
-- statement:
--   The Global Theory construction uses the adjoin hom extend of denominator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdjoinHomExtendOfDenominator.lean#L6-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdjoinHomExtendOfDenominator.lean#L6-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NonemptyAlgHomAdjoin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinHomExtendOfDenominator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.adjoin_hom_extend_of_denominator (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω]
    [Algebra k Ω] (S : Subalgebra k F) (ψ : S →ₐ[k] Ω) (h : S) (hψ : ψ h ≠ 0) (T : Set F)
    (hT : ∀ x ∈ T, (h : F) * x ∈ S) : Nonempty (Algebra.adjoin k T →ₐ[k] Ω) := by sorry
