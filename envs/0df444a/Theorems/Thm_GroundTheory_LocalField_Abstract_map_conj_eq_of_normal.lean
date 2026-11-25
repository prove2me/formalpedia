-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_map_conj_eq_of_normal
-- name    : GroundTheory.LocalField.Abstract.map_conj_eq_of_normal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:36:05.34388+00:00
-- url     : https://prove2.me/theorems/b13e9898-4e8d-4113-9acc-ebd72176b5e3
-- title:
--   Abstract: map conj eq of normal
-- statement:
--   The Abstract construction uses the map conj eq of normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/FunctorialityTransfer.lean#L114-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/FunctorialityTransfer.lean#L114-L124

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityTransfer
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
open ProfiniteInteger MulAction
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

theorem GroundTheory.LocalField.Abstract.map_conj_eq_of_normal {K L : Subgroup G} [(L.subgroupOf K).Normal] (hLK : L ≤ K) {τ : G}
    (hτ : τ ∈ K) : L.map (MulAut.conj τ).toMonoidHom = L := by sorry
