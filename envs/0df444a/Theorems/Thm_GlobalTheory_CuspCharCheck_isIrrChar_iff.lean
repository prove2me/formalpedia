-- Prove2me | Theorems.Thm_GlobalTheory_CuspCharCheck_isIrrChar_iff
-- name    : GlobalTheory.CuspCharCheck.isIrrChar_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:30:01.891161+00:00
-- url     : https://prove2.me/theorems/c5e8fc51-58b5-4d75-96ef-6792d1f99b73
-- title:
--   Cusp Char Check: is Irr Char iff
-- statement:
--   The Cusp Char Check construction uses the is Irr Char iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L31-L38

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_SubgroupCharacterSums_SumSubgroupEqZeroIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CuspElliptic
open GlobalTheory GlobalTheory.CuspCharCheck
variable {G : Type} [Group G]

theorem GlobalTheory.CuspCharCheck.isIrrChar_iff [Fintype G] (χ : G → ℂ) : IsIrrChar χ ↔ ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ := by sorry
