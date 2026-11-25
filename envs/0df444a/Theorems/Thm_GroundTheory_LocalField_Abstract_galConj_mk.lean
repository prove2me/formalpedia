-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_galConj_mk
-- name    : GroundTheory.LocalField.Abstract.galConj_mk
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:43:05.21723+00:00
-- url     : https://prove2.me/theorems/dfa74e5d-0d37-4c88-8dc8-75006bd11251
-- title:
--   Abstract: gal Conj mk
-- statement:
--   The Abstract construction uses the gal Conj mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Functoriality.lean#L151-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Functoriality.lean#L151-L155

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ReciprocityMap
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Functoriality
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
open ProfiniteInteger
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A]
omit [CompactSpace G]

theorem GroundTheory.LocalField.Abstract.galConj_mk (σ : G) (K L : OpenSubgroup G) [((L : Subgroup G).subgroupOf K).Normal]
    (τ : (K : Subgroup G)) :
    galConj σ K L (τ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      ((⟨σ * τ * σ⁻¹, τ, τ.2, rfl⟩ : ((conjOpen σ K : OpenSubgroup G) : Subgroup G)) : _ ⧸ _) := by sorry
