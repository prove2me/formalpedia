-- Prove2me | Theorems.Thm_GlobalTheory_mkQ_mem_smul_top_iff_mem_sup
-- name    : GlobalTheory.mkQ_mem_smul_top_iff_mem_sup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:41.746197+00:00
-- url     : https://prove2.me/theorems/6a741bbd-5ebe-4306-bac0-83b24e600974
-- title:
--   Global Theory: mk Q mem smul top iff mem sup
-- statement:
--   The Global Theory construction uses the mk Q mem smul top iff mem sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FlatQuotientWeaklyRegular.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FlatQuotientWeaklyRegular.lean#L7-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatCokerOfInjectiveModMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatQuotientWeaklyRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.mkQ_mem_smul_top_iff_mem_sup {A : Type} [CommRing A] (J I : Ideal A) (a : A) :
    Submodule.mkQ J a ∈ (I • ⊤ : Submodule A (A ⧸ J)) ↔ a ∈ J ⊔ I := by sorry
