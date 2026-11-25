-- Prove2me | Theorems.Thm_GlobalTheory_CuspCharCheck_isCuspChar_rank_one
-- name    : GlobalTheory.CuspCharCheck.isCuspChar_rank_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:04:15.69781+00:00
-- url     : https://prove2.me/theorems/65acd405-3d23-400c-a7ac-d9a130e86d7a
-- title:
--   Cusp Char Check: is Cusp Char rank one
-- statement:
--   The Cusp Char Check construction uses the is Cusp Char rank one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L150-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L150-L151

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

theorem GlobalTheory.CuspCharCheck.isCuspChar_rank_one (c : GL (Fin 1) F →* ℂˣ) : IsCuspChar (fun x => (c x : ℂ)) := by sorry
