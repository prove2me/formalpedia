-- Prove2me | Theorems.Thm_GlobalTheory_T_index_sqs_of_fg
-- name    : GlobalTheory.T.index_sqs_of_fg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:46:20.911542+00:00
-- url     : https://prove2.me/theorems/944f35e4-ba77-4c92-99a8-8965f7a0b3d0
-- title:
--   T: index sqs of fg
-- statement:
--   The T construction uses the index sqs of fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexSqsTopOfFgStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexSqsTopOfFgStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexSqsTopOfFg
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexSqsTopOfFgStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.index_sqs_of_fg : ∀ (G : Type) [CommGroup G] [Group.FG G], (sqs (⊤ : Subgroup G)).index = 2 ^ Module.finrank ℤ (Additive G) * Nat.card {a : G // a ^ 2 = 1} := by sorry
