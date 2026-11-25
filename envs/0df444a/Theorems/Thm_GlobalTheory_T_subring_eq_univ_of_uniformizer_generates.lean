-- Prove2me | Theorems.Thm_GlobalTheory_T_subring_eq_univ_of_uniformizer_generates
-- name    : GlobalTheory.T.subring_eq_univ_of_uniformizer_generates
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:38:55.484555+00:00
-- url     : https://prove2.me/theorems/ff3d908a-b967-5dd6-a0b4-c97cb0ea5a8e
-- title:
--   T: subring eq univ of uniformizer generates
-- statement:
--   The T construction uses the subring eq univ of uniformizer generates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvrSubringEqTopStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvrSubringEqTopStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvrSubringEqTop
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvrSubringEqTopStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.subring_eq_univ_of_uniformizer_generates : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (S : Subring V) (π : V), π ∈ S → π ≠ 0 → π ∈ IsLocalRing.maximalIdeal V → (∀ s ∈ S, s ∉ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s * t = 1) → (∀ s ∈ S, s ∈ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s = π * t) → (∀ v : V, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ v * b = a) → S = ⊤ := by sorry
