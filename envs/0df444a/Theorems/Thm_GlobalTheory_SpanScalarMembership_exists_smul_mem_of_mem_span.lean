-- Prove2me | Theorems.Thm_GlobalTheory_SpanScalarMembership_exists_smul_mem_of_mem_span
-- name    : GlobalTheory.SpanScalarMembership.exists_smul_mem_of_mem_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:45.85001+00:00
-- url     : https://prove2.me/theorems/93a8abd9-99a3-4628-9d5c-fc8774ca0139
-- title:
--   Span Scalar Membership: exists smul mem of mem span
-- statement:
--   The Span Scalar Membership construction uses the exists smul mem of mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ImportsTer.lean#L7-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ImportsTer.lean#L7-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ImportsTer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SpanScalarMembership
open NumberField

theorem GlobalTheory.SpanScalarMembership.exists_smul_mem_of_mem_span {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    (T : Submodule (RingOfIntegers K) V) {x : V} (hx : x ∈ Submodule.span K (T : Set V)) :
    ∃ s : RingOfIntegers K, s ≠ 0 ∧ s • x ∈ T := by sorry
