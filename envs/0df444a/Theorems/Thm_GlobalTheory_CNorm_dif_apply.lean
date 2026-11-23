-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_dif_apply
-- name    : GlobalTheory.CNorm.dif_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:04:25.772561+00:00
-- url     : https://prove2.me/theorems/5d430ea1-077a-4e9d-8019-f6d6984260cd
-- title:
--   CNorm: dif apply
-- statement:
--   The CNorm construction uses the dif apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/MemPowSub.lean#L33-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/MemPowSub.lean#L33-L33

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

theorem GlobalTheory.CNorm.dif_apply {A : Type} [CommGroup A] (σ : A →* A) (a : A) : dif σ a = σ a / a := by sorry
