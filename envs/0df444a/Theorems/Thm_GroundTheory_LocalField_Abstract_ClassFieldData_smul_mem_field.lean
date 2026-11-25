-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_smul_mem_field
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.smul_mem_field
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:36:37.94554+00:00
-- url     : https://prove2.me/theorems/6b8d6f2f-1e9f-4597-98ba-71160ee9b449
-- title:
--   Class Field Data: smul mem field
-- statement:
--   The Class Field Data construction uses the smul mem field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L114-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L114-L122

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

theorem GroundTheory.LocalField.Abstract.ClassFieldData.smul_mem_field [IsDiscreteModule G A] (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (s : D.FrobeniusLift K) {g : G}
    (hgJ : ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker),
      g • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker))
    (hcomm : ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker), s.elt • g • y = g • s.elt • y)
    {y : A} (hy : y ∈ fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)) :
    g • y ∈ fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G) := by sorry
