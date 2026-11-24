-- Prove2me | Theorems.Thm_GlobalTheory_exists_mem_valuation_le_of_mem_span
-- name    : GlobalTheory.exists_mem_valuation_le_of_mem_span
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:35:21.738562+00:00
-- url     : https://prove2.me/theorems/fbd90ab1-68e4-473f-9f30-5e50f18d6a64
-- title:
--   Global Theory: exists mem valuation le of mem span
-- statement:
--   The Global Theory construction uses the exists mem valuation le of mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsLeadingMinorsGeOfLeRank.lean#L6-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsLeadingMinorsGeOfLeRank.lean#L6-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLeadingMinorsGeOfLeRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_mem_valuation_le_of_mem_span {C : Type} [Field C] (v : Valuation C NNReal)
    {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) {M : Type} [AddCommGroup M]
    [Module O M] (A : Set M) (φ : M →ₗ[O] O) {x : M} (hx : x ∈ Submodule.span O A)
    (h0 : v (algebraMap O C (φ x)) ≠ 0) :
    ∃ a ∈ A, v (algebraMap O C (φ x)) ≤ v (algebraMap O C (φ a)) := by sorry
