-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm_congr
-- name    : GroundTheory.LocalField.Abstract.coe_norm_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:24.580117+00:00
-- url     : https://prove2.me/theorems/616a8f4d-846f-4ed1-a5fa-3544d3a9c02c
-- title:
--   Abstract: coe norm congr
-- statement:
--   The Abstract construction uses the coe norm congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/NormFormula.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/NormFormula.lean#L21-L26

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

theorem GroundTheory.LocalField.Abstract.coe_norm_congr {K K' L L' : Subgroup G} (hK : K = K') (hL : L = L')
    [(L.subgroupOf K).FiniteIndex] [(L'.subgroupOf K').FiniteIndex] (a : fixedModule A L) :
    (norm A K L a : A) = norm A K' L' ⟨a, hL ▸ a.2⟩ := by sorry
