-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_smul_norm
-- name    : GroundTheory.LocalField.Abstract.smul_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:04:00.487173+00:00
-- url     : https://prove2.me/theorems/bca2af40-9d21-4d16-869e-42cb2df5957a
-- title:
--   Abstract: smul norm
-- statement:
--   The Abstract construction uses the smul norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/UniqueQuotientSubgroupOfSelf.lean#L145-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/UniqueQuotientSubgroupOfSelf.lean#L145-L184

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Theorems.Thm_GroundTheory_LocalField_Abstract_smul_mem_fixedModule

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

theorem GroundTheory.LocalField.Abstract.smul_norm (σ : G) [(L.subgroupOf K).FiniteIndex]
    [((L.map (MulAut.conj σ).toMonoidHom).subgroupOf (K.map (MulAut.conj σ).toMonoidHom)).FiniteIndex]
    (a : fixedModule A L) :
    σ • (norm A K L a : A) =
      norm A (K.map (MulAut.conj σ).toMonoidHom) (L.map (MulAut.conj σ).toMonoidHom)
        ⟨σ • (a : A), smul_mem_fixedModule a.2 σ⟩ := by sorry
