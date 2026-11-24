-- Prove2me | Theorems.Thm_GlobalTheory_CuspCharCheck_isCuspChar_iff
-- name    : GlobalTheory.CuspCharCheck.isCuspChar_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:30:58.336679+00:00
-- url     : https://prove2.me/theorems/7eb23219-cf1b-4cab-8665-27b2daa7b340
-- title:
--   Cusp Char Check: is Cusp Char iff
-- statement:
--   The Cusp Char Check construction uses the is Cusp Char iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L119-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L119-L133

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

theorem GlobalTheory.CuspCharCheck.isCuspChar_iff {d : ℕ} (χ : GL (Fin d) F → ℂ) :
    IsCuspChar χ ↔ ∃ V : FDRep ℂ (GL (Fin d) F), Simple V ∧ V.character = χ ∧
      ∀ a, 0 < a → a < d → ∀ v : V, (∀ u ∈ (unipSubgroup d a : Subgroup (GL (Fin d) F)), V.ρ u v = v) → v = 0 := by sorry
