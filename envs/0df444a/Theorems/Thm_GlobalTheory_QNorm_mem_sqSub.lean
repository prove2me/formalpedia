-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_mem_sqSub
-- name    : GlobalTheory.QNorm.mem_sqSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:58.20777+00:00
-- url     : https://prove2.me/theorems/5d6ffcb6-0bd2-4518-8e6b-700091386303
-- title:
--   QNorm: mem sq Sub
-- statement:
--   The QNorm construction uses the mem sq Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/SqSubLeNormSub.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/SqSubLeNormSub.lean#L35-L36

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

theorem GlobalTheory.QNorm.mem_sqSub {F L : Type} [Field F] [Field L] (φ : F →+* L) (x : Fˣ) :
    x ∈ sqSub φ ↔ IsSquare (φ (x : F)) := by sorry
