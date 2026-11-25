-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_exists_norm_eq_norm_inf_ker
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.exists_norm_eq_norm_inf_ker
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:35:14.323797+00:00
-- url     : https://prove2.me/theorems/66f1fc2a-77fb-4a8c-bde0-6a3e656a0425
-- title:
--   Class Field Data: exists norm eq norm inf ker
-- statement:
--   The Class Field Data construction uses the exists norm eq norm inf ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L229-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L229-L418

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
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
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

theorem GroundTheory.LocalField.Abstract.ClassFieldData.exists_norm_eq_norm_inf_ker (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂))
    (s1 s2 : D.FrobeniusLift K) (h1 : s1.elt = φ ^ s1.deg) (hψL : s1.elt ∈ (L : Subgroup G))
    (h2 : s2.elt = s1.elt ^ ((L : Subgroup G).relIndex K))
    (hdeg : s2.deg = (L : Subgroup G).relIndex K * s1.deg)
    {x a : A} (hx : x ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G))
    (ha : a ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G))
    (hxu : D.valuation (s1.field L hLK) ⟨x, hx⟩ = 1)
    (hau : D.valuation (s1.field L hLK) ⟨a, ha⟩ = 1)
    {δ : G} (hδ : δ ∈ (K : Subgroup G) ⊓ D.deg.ker) (hrel : φ • x / x = δ • a / a) :
    ∃ b : fixedModule A (L : Subgroup G),
      (norm A (K : Subgroup G) (L : Subgroup G) b : A) =
        norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
          ⟨x, fixedModule_anti le_frobeniusClosure hx⟩ := by sorry
