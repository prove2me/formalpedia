-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_mem_powSub
-- name    : GlobalTheory.CNorm.mem_powSub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:09.209664+00:00
-- url     : https://prove2.me/theorems/c845a8f8-58e7-4520-bbbc-57051f0f3e49
-- title:
--   CNorm: mem pow Sub
-- statement:
--   The CNorm construction uses the mem pow Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/MemPowSub.lean#L55-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/MemPowSub.lean#L55-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CNorm
open NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem GlobalTheory.CNorm.mem_powSub (p : ℕ) {F L : Type} [Field F] [Field L] (φ : F →+* L)
    (x : Fˣ) : x ∈ _root_.GlobalTheory.CNorm.powSub p φ ↔ ∃ r : L, r ^ p = φ (x : F) := by sorry
