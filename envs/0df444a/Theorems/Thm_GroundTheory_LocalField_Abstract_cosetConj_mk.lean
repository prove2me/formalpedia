-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
-- name    : GroundTheory.LocalField.Abstract.cosetConj_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:03.97455+00:00
-- url     : https://prove2.me/theorems/e13d0959-f37d-4fae-bad2-0f32a41e3760
-- title:
--   Abstract: coset Conj mk
-- statement:
--   The Abstract construction uses the coset Conj mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/UniqueQuotientSubgroupOfSelf.lean#L140-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/UniqueQuotientSubgroupOfSelf.lean#L140-L143

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
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
variable {K L : Subgroup G}

theorem GroundTheory.LocalField.Abstract.cosetConj_mk (σ : G) (τ : K) :
    cosetConj (L := L) σ (τ : K ⧸ L.subgroupOf K) =
      ((⟨σ * τ * σ⁻¹, τ, τ.2, rfl⟩ : K.map (MulAut.conj σ).toMonoidHom) : _ ⧸ _) := by sorry

attribute [defeq] GroundTheory.LocalField.Abstract.cosetConj_mk
