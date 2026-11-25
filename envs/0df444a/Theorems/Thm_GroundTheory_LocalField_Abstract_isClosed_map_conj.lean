-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_isClosed_map_conj
-- name    : GroundTheory.LocalField.Abstract.isClosed_map_conj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:51:14.418329+00:00
-- url     : https://prove2.me/theorems/1cfa6730-8b8d-49ab-9349-80910f70c030
-- title:
--   Abstract: is Closed map conj
-- statement:
--   The Abstract construction uses the is Closed map conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Functoriality.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Functoriality.lean#L37-L40

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
variable {G : Type*} [Group G]
variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem GroundTheory.LocalField.Abstract.isClosed_map_conj {H : Subgroup G} (hH : IsClosed (H : Set G)) (σ : G) :
    IsClosed (H.map (MulAut.conj σ).toMonoidHom : Set G) := by sorry
