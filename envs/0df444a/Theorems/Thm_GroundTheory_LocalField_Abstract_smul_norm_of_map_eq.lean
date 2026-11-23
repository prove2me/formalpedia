-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_smul_norm_of_map_eq
-- name    : GroundTheory.LocalField.Abstract.smul_norm_of_map_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:17.798524+00:00
-- url     : https://prove2.me/theorems/8217c7b6-89de-411a-aefa-41b25d529634
-- title:
--   Abstract: smul norm of map eq
-- statement:
--   The Abstract construction uses the smul norm of map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/NormFormula.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/NormFormula.lean#L28-L38

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
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

theorem GroundTheory.LocalField.Abstract.smul_norm_of_map_eq {K L : Subgroup G} (g : G) (hK : K.map (MulAut.conj g).toMonoidHom = K)
    (hL : L.map (MulAut.conj g).toMonoidHom = L) [(L.subgroupOf K).FiniteIndex]
    (a : fixedModule A L) :
    g • (norm A K L a : A) = norm A K L ⟨g • (a : A), by
      have := smul_mem_fixedModule a.2 g
      rwa [hL] at this⟩ := by sorry
