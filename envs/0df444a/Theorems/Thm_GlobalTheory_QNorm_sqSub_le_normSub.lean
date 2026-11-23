-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_sqSub_le_normSub
-- name    : GlobalTheory.QNorm.sqSub_le_normSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:26:15.029161+00:00
-- url     : https://prove2.me/theorems/a547b645-3b04-4835-97a6-a20bf254cb6c
-- title:
--   QNorm: sq Sub le norm Sub
-- statement:
--   The QNorm construction uses the sq Sub le norm Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/SqSubLeNormSub.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/SqSubLeNormSub.lean#L41-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped WithZero
noncomputable section
open GlobalTheory GlobalTheory.QNorm

theorem GlobalTheory.QNorm.sqSub_le_normSub {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) :
    sqSub φ ≤ normSub φ δ := by sorry
