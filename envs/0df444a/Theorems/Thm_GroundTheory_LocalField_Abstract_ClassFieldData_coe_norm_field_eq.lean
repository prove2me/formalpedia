-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_coe_norm_field_eq
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.coe_norm_field_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:35:58.258047+00:00
-- url     : https://prove2.me/theorems/7cbd74a0-6023-433d-bab9-8764ce03e83a
-- title:
--   Class Field Data: coe norm field eq
-- statement:
--   The Class Field Data construction uses the coe norm field eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/CoeNormEqProdSmulNorm.lean#L151-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/CoeNormEqProdSmulNorm.lean#L151-L178

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Reciprocity
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Theorems.Thm_GroundTheory_LocalField_Abstract_fixedModule_anti
import Theorems.Thm_GroundTheory_LocalField_Abstract_le_frobeniusClosure

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
variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
open GroundTheory.LocalField.Abstract.ClassFieldData
variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] (s : D.FrobeniusLift K)

theorem GroundTheory.LocalField.Abstract.ClassFieldData.coe_norm_field_eq {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂))
    (a : fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)) :
    (norm A (K : Subgroup G) (s.field L hLK : Subgroup G) a : A) =
      ∏ ν : Fin s.deg, φ ^ (ν : ℕ) •
        (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
          ⟨a, fixedModule_anti le_frobeniusClosure a.2⟩ : A) := by sorry
