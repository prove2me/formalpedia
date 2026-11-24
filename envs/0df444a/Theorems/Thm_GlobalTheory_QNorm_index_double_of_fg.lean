-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_index_double_of_fg
-- name    : GlobalTheory.QNorm.index_double_of_fg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:02:12.97773+00:00
-- url     : https://prove2.me/theorems/a3d72043-7f28-40ec-89ec-b85a997e129e
-- title:
--   QNorm: index double of fg
-- statement:
--   The QNorm construction uses the index double of fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexSqsTopOfFg.lean#L52-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexSqsTopOfFg.lean#L52-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexSqsTopOfFg
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
open GlobalTheory GlobalTheory.QNorm

theorem GlobalTheory.QNorm.index_double_of_fg (M : Type) [AddCommGroup M] [AddGroup.FG M] :
    (nsmulAddMonoidHom (α := M) 2).range.index =
      2 ^ Module.finrank ℤ M * Nat.card (nsmulAddMonoidHom (α := M) 2).ker := by sorry
