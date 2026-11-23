-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_mem_fix
-- name    : GlobalTheory.CNorm.mem_fix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:00.981823+00:00
-- url     : https://prove2.me/theorems/4a565b98-dcf0-45c9-95f6-a16d16f0a6aa
-- title:
--   CNorm: mem fix
-- statement:
--   The CNorm construction uses the mem fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/MemPowSub.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/MemPowSub.lean#L37-L38

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

theorem GlobalTheory.CNorm.mem_fix {A : Type} [CommGroup A] (σ : A →* A) (a : A) :
    a ∈ _root_.GlobalTheory.CNorm.fix σ ↔ σ a = a := by sorry
