-- Prove2me | Theorems.Thm_GlobalTheory_Nef_exists_fin_enum_multiset
-- name    : GlobalTheory.Nef.exists_fin_enum_multiset
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:01:54.310251+00:00
-- url     : https://prove2.me/theorems/995f49c4-7c25-4831-aed9-fd0af8eff7f3
-- title:
--   Nef: exists fin enum multiset
-- statement:
--   The Nef construction uses the exists fin enum multiset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BinaryFormSplits.lean#L9-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BinaryFormSplits.lean#L9-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BinaryFormSplits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef

theorem GlobalTheory.Nef.exists_fin_enum_multiset {α : Type} : ∀ (n : ℕ) (M : Multiset α), Multiset.card M = n →
    ∃ u : Fin n → α, Multiset.map u Finset.univ.val = M := by sorry
