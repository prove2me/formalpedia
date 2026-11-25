-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_coe_norm_inf_ker_mul
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.coe_norm_inf_ker_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:14:53.050697+00:00
-- url     : https://prove2.me/theorems/0b09ad40-6453-5a97-b8e6-a73b0f169129
-- title:
--   Class Field Data: coe norm inf ker mul
-- statement:
--   The Class Field Data construction uses the coe norm inf ker mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L212-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L212-L221

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
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
omit [TotallyDisconnectedSpace G] [((L : Subgroup G).subgroupOf K).Normal]

theorem GroundTheory.LocalField.Abstract.ClassFieldData.coe_norm_inf_ker_mul {y z : A} (hy : y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker))
    (hz : z ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) :
    (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
      ⟨y * z, Subgroup.mul_mem _ hy hz⟩ : A) =
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨y, hy⟩ : A) *
        norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨z, hz⟩ := by sorry
