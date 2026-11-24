-- Prove2me | Theorems.Thm_GlobalTheory_CuspCharCheck_isIrrChar_of_hom
-- name    : GlobalTheory.CuspCharCheck.isIrrChar_of_hom
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:51.712295+00:00
-- url     : https://prove2.me/theorems/7a1d26a9-71ef-4e4d-8882-616b8c1c667c
-- title:
--   Cusp Char Check: is Irr Char of hom
-- statement:
--   The Cusp Char Check construction uses the is Irr Char of hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L138-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/SubgroupCharacterSums/SumSubgroupEqZeroIff.lean#L138-L148

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

theorem GlobalTheory.CuspCharCheck.isIrrChar_of_hom {G : Type} [Group G] [Fintype G] (c : G →* ℂˣ) : IsIrrChar (fun x => (c x : ℂ)) := by sorry
