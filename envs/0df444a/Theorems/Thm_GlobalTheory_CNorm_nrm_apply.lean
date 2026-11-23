-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_nrm_apply
-- name    : GlobalTheory.CNorm.nrm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:43.559434+00:00
-- url     : https://prove2.me/theorems/7fd38046-6b6d-4de1-bc14-362bf775cdb4
-- title:
--   CNorm: nrm apply
-- statement:
--   The CNorm construction uses the nrm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/MemPowSub.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/MemPowSub.lean#L30-L31

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

theorem GlobalTheory.CNorm.nrm_apply {A : Type} [CommGroup A] (σ : A →* A) (n : ℕ) (a : A) :
    nrm σ n a = ∏ i ∈ Finset.range n, σ^[i] a := by sorry
