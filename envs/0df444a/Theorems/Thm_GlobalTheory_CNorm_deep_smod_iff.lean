-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_deep_smod_iff
-- name    : GlobalTheory.CNorm.deep_smod_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:07:10.011575+00:00
-- url     : https://prove2.me/theorems/6b5243fa-c68d-4dd3-9231-006c70c77917
-- title:
--   CNorm: deep smod iff
-- statement:
--   The CNorm construction uses the deep smod iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SubgroupPowImageUnitsCongruentOneModOfIsAdicComp.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SubgroupPowImageUnitsCongruentOneModOfIsAdicComp.lean#L9-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SubgroupPowImageUnitsCongruentOneModOfIsAdicComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm

theorem GlobalTheory.CNorm.deep_smod_iff {O : Type} [CommRing O] (π a b : O) (n : ℕ) :
    a ≡ b [SMOD (Ideal.span {π} ^ n • ⊤ : Submodule O O)] ↔ π ^ n ∣ a - b := by sorry
