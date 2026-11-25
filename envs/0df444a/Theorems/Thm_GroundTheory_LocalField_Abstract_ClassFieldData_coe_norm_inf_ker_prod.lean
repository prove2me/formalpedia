-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_coe_norm_inf_ker_prod
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.coe_norm_inf_ker_prod
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:47:29.827467+00:00
-- url     : https://prove2.me/theorems/33f86a2b-ea57-4070-959f-c00f52e2614a
-- title:
--   Class Field Data: coe norm inf ker prod
-- statement:
--   The Class Field Data construction uses the coe norm inf ker prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L197-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L197-L208

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

theorem GroundTheory.LocalField.Abstract.ClassFieldData.coe_norm_inf_ker_prod {ι : Type*} (s : Finset ι) (f : ι → A)
    (hf : ∀ i, f i ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) :
    (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
      ⟨∏ i ∈ s, f i, Subgroup.prod_mem _ fun i _ => hf i⟩ : A) =
      ∏ i ∈ s, (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨f i, hf i⟩ : A) := by sorry
