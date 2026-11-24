-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm_eq_of_mul_eq
-- name    : GroundTheory.LocalField.Abstract.coe_norm_eq_of_mul_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:44:39.050845+00:00
-- url     : https://prove2.me/theorems/ca6e684f-bcab-48a8-abc1-9f49cae93063
-- title:
--   Abstract: coe norm eq of mul eq
-- statement:
--   The Abstract construction uses the coe norm eq of mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/NormFormula.lean#L40-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/NormFormula.lean#L40-L74

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]

theorem GroundTheory.LocalField.Abstract.coe_norm_eq_of_mul_eq {K S Q J : Subgroup G} (hQK : Q ≤ K)
    (hmul : ∀ k ∈ K, ∃ q ∈ Q, q⁻¹ * k ∈ S) (hJ : ∀ q ∈ Q, q ∈ S ↔ q ∈ J)
    [(S.subgroupOf K).FiniteIndex] [(J.subgroupOf Q).FiniteIndex] (a : fixedModule A S)
    (ha : (a : A) ∈ fixedModule A J) :
    (norm A K S a : A) = norm A Q J ⟨a, ha⟩ := by sorry
