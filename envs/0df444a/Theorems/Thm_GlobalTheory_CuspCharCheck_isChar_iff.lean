-- Prove2me | Theorems.Thm_GlobalTheory_CuspCharCheck_isChar_iff
-- name    : GlobalTheory.CuspCharCheck.isChar_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:43.634354+00:00
-- url     : https://prove2.me/theorems/768614b6-79f4-4fb2-80bc-677527be4e6a
-- title:
--   Cusp Char Check: is Char iff
-- statement:
--   The Cusp Char Check construction uses the is Char iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L12-L24

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

theorem GlobalTheory.CuspCharCheck.isChar_iff (χ : G → ℂ) : IsChar χ ↔ ∃ V : FDRep ℂ G, V.character = χ := by sorry
