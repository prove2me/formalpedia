-- Prove2me | Theorems.Thm_GlobalTheory_CuspCharCheck_not_isCuspChar_one
-- name    : GlobalTheory.CuspCharCheck.not_isCuspChar_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:04:17.740294+00:00
-- url     : https://prove2.me/theorems/825cbf37-0f2a-4268-84f3-cd84e0e8f986
-- title:
--   Cusp Char Check: not is Cusp Char one
-- statement:
--   The Cusp Char Check construction uses the not is Cusp Char one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L153-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L153-L158

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

theorem GlobalTheory.CuspCharCheck.not_isCuspChar_one {d : ℕ} (hd : 2 ≤ d) : ¬ IsCuspChar (fun _ : GL (Fin d) F => (1 : ℂ)) := by sorry
