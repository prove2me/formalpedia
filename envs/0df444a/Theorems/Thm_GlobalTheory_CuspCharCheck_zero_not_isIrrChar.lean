-- Prove2me | Theorems.Thm_GlobalTheory_CuspCharCheck_zero_not_isIrrChar
-- name    : GlobalTheory.CuspCharCheck.zero_not_isIrrChar
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:05:09.271809+00:00
-- url     : https://prove2.me/theorems/26115afc-6d05-4782-a4f1-1d219b243c10
-- title:
--   Cusp Char Check: zero not is Irr Char
-- statement:
--   The Cusp Char Check construction uses the zero not is Irr Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L60-L63

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

theorem GlobalTheory.CuspCharCheck.zero_not_isIrrChar [Fintype G] : ¬ IsIrrChar (fun _ : G => (0 : ℂ)) := by sorry
