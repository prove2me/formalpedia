-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_mem_normSub
-- name    : GlobalTheory.QNorm.mem_normSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:26:01.013801+00:00
-- url     : https://prove2.me/theorems/fc32e849-8db7-4d46-ac07-357240a3064b
-- title:
--   QNorm: mem norm Sub
-- statement:
--   The QNorm construction uses the mem norm Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/SqSubLeNormSub.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/SqSubLeNormSub.lean#L38-L39

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

theorem GlobalTheory.QNorm.mem_normSub {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) (x : Fˣ) :
    x ∈ normSub φ δ ↔ ∃ a b : L, φ (x : F) = a ^ 2 - φ δ * b ^ 2 := by sorry
