-- Prove2me | Theorems.Thm_GlobalTheory_CuspCharCheck_isCuspChar_of_hom
-- name    : GlobalTheory.CuspCharCheck.isCuspChar_of_hom
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:30:54.600743+00:00
-- url     : https://prove2.me/theorems/496dddc8-f4c3-49b9-a1df-556c474528ef
-- title:
--   Cusp Char Check: is Cusp Char of hom
-- statement:
--   The Cusp Char Check construction uses the is Cusp Char of hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L160-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L160-L174

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

theorem GlobalTheory.CuspCharCheck.isCuspChar_of_hom {d : ℕ} (c : GL (Fin d) F →* ℂˣ)
    (hc : ∀ a, 0 < a → a < d → ∃ t ∈ (unipBlock d a : Set (GL (Fin d) F)), (c t : ℂ) ≠ 1) :
    IsCuspChar (fun x => (c x : ℂ)) := by sorry
