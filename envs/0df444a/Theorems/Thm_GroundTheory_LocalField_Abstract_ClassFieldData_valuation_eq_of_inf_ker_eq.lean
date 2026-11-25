-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_eq_of_inf_ker_eq
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.valuation_eq_of_inf_ker_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:35:42.756963+00:00
-- url     : https://prove2.me/theorems/73d88ec9-998b-44c1-a8f8-5845d99b261a
-- title:
--   Class Field Data: valuation eq of inf ker eq
-- statement:
--   The Class Field Data construction uses the valuation eq of inf ker eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Multiplicative.lean#L90-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Multiplicative.lean#L90-L105

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Multiplicative
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
omit [TotallyDisconnectedSpace G]

theorem GroundTheory.LocalField.Abstract.ClassFieldData.valuation_eq_of_inf_ker_eq {S P : OpenSubgroup G}
    (h : (S : Subgroup G) ⊓ D.deg.ker = (P : Subgroup G) ⊓ D.deg.ker) {y : A}
    (hyS : y ∈ fixedModule A (S : Subgroup G)) (hyP : y ∈ fixedModule A (P : Subgroup G)) :
    D.valuation P ⟨y, hyP⟩ = D.valuation S ⟨y, hyS⟩ := by sorry
