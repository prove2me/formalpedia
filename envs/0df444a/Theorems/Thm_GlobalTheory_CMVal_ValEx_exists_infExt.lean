-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_ValEx_exists_infExt
-- name    : GlobalTheory.CMVal.ValEx.exists_infExt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:06:47.629809+00:00
-- url     : https://prove2.me/theorems/f365c380-8c37-4bcc-97f6-6377a4b83f81
-- title:
--   Val Ex: exists inf Ext
-- statement:
--   The Val Ex construction uses the exists inf Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L257-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L257-L275

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.ValEx.exists_infExt (φ : E →+* ℂ) :
    ∃ e : InfiniteAdeleRing E →+* ℂ, Continuous e ∧ (∀ k : E, e (algebraMap E _ k) = φ k) ∧
      ∀ x y : InfiniteAdeleRing E, x (InfinitePlace.mk φ) = y (InfinitePlace.mk φ) → e x = e y := by sorry
