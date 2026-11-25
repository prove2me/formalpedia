-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_reciprocity_mk_conj_pow
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.reciprocity_mk_conj_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:04.533402+00:00
-- url     : https://prove2.me/theorems/30741c4e-8130-4aac-a0b8-b024dff34196
-- title:
--   Class Field Data: reciprocity mk conj pow
-- statement:
--   The Class Field Data construction uses the reciprocity mk conj pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/FunctorialityTransfer.lean#L212-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/FunctorialityTransfer.lean#L212-L292

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityTransfer
import Theorems.Thm_GroundTheory_LocalField_Abstract_fixedModule_anti
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
open ProfiniteInteger MulAction
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A}
variable {K K' L : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
  [((L : Subgroup G).subgroupOf K').Normal]

theorem GroundTheory.LocalField.Abstract.ClassFieldData.reciprocity_mk_conj_pow (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    (hLK' : L ≤ K') (hK'K : K' ≤ K) (s : D.FrobeniusLift K) (x : (K : Subgroup G)) {f : ℕ}
    (hf0 : 0 < f) (hf : ∀ k : ℤ, (x : G)⁻¹ * s.elt ^ k * x ∈ (K' : Subgroup G) ↔ (f : ℤ) ∣ k)
    (hmem : (x : G)⁻¹ * s.elt ^ f * x ∈ (K' : Subgroup G))
    {π : fixedModule A ((s.field L (hLK'.trans hK'K) : OpenSubgroup G) : Subgroup G)}
    (hπ : D.valuation (s.field L (hLK'.trans hK'K)) π = Multiplicative.ofAdd 1) :
    D.reciprocity hLK' hax ((⟨_, hmem⟩ : (K' : Subgroup G)) :
      (K' : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K') =
      (QuotientGroup.mk (norm A (K' : Subgroup G)
        ((K' ⊓ conjOpen (x : G)⁻¹ (s.field L (hLK'.trans hK'K)) : OpenSubgroup G) : Subgroup G)
        ⟨(x : G)⁻¹ • (π : A), fixedModule_anti (inf_le_right (a := K'))
          (smul_mem_fixedModule π.2 _)⟩) : tateZero A (K' : Subgroup G) (L : Subgroup G)) := by sorry
