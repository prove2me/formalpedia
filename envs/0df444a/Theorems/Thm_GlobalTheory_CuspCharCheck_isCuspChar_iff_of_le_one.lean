-- Prove2me | Theorems.Thm_GlobalTheory_CuspCharCheck_isCuspChar_iff_of_le_one
-- name    : GlobalTheory.CuspCharCheck.isCuspChar_iff_of_le_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:29:57.008272+00:00
-- url     : https://prove2.me/theorems/db773de5-ba9e-45bd-a30f-521c4fd72f70
-- title:
--   Cusp Char Check: is Cusp Char iff of le one
-- statement:
--   The Cusp Char Check construction uses the is Cusp Char iff of le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L135-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L135-L136

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
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem GlobalTheory.CuspCharCheck.isCuspChar_iff_of_le_one {d : ℕ} (hd : d ≤ 1) (χ : GL (Fin d) F → ℂ) : IsCuspChar χ ↔ IsIrrChar χ := by sorry
