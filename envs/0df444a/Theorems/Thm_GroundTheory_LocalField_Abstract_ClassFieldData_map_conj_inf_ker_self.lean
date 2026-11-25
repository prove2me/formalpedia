-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_map_conj_inf_ker_self
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.map_conj_inf_ker_self
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:36:02.441033+00:00
-- url     : https://prove2.me/theorems/92beb6dd-ac52-48c3-83d0-706f8ff4ea6e
-- title:
--   Class Field Data: map conj inf ker self
-- statement:
--   The Class Field Data construction uses the map conj inf ker self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L67-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L67-L73

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
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
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
omit [TotallyDisconnectedSpace G]

theorem GroundTheory.LocalField.Abstract.ClassFieldData.map_conj_inf_ker_self {g : G} (hg : g ∈ (K : Subgroup G)) :
    ((K : Subgroup G) ⊓ D.deg.ker).map (MulAut.conj g).toMonoidHom =
      (K : Subgroup G) ⊓ D.deg.ker := by sorry
