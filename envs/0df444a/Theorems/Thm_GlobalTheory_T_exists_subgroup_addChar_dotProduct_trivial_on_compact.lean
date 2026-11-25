-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_subgroup_addChar_dotProduct_trivial_on_compact
-- name    : GlobalTheory.T.exists_subgroup_addChar_dotProduct_trivial_on_compact
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:31:16.302516+00:00
-- url     : https://prove2.me/theorems/0c80c7e6-d827-4150-957b-17f7685105a6
-- title:
--   T: exists subgroup add Char dot Product trivial on compact
-- statement:
--   The T construction uses the exists subgroup add Char dot Product trivial on compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSubgroupAddCharDotProductTrivialOnCompactStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSubgroupAddCharDotProductTrivialOnCompactStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSubgroupAddCharDotProductTrivialOnCompact
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSubgroupAddCharDotProductTrivialOnCompactStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_subgroup_addChar_dotProduct_trivial_on_compact : ∀ {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [NonarchimedeanAddGroup K] (χ : AddChar K ℂ), Continuous χ → ∀ (κ : Type) [Fintype κ] (C : Set (κ → K)), IsCompact C → ∃ H : OpenAddSubgroup (κ → K), ∀ z ∈ C, ∀ a ∈ H, ∀ b ∈ H, χ (z ⬝ᵥ b + a ⬝ᵥ b) = 1 := by sorry
