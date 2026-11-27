-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_reciprocity_frobenius_of_unramified
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.reciprocity_frobenius_of_unramified
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:11:21.43318+00:00
-- url     : https://prove2.me/theorems/92bbcd5d-87ed-4540-abb0-7bf2466a7529
-- title:
--   Class Field Data: reciprocity frobenius of unramified
-- statement:
--   The Class Field Data construction uses the reciprocity frobenius of unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/IsoCyclic.lean#L176-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/IsoCyclic.lean#L176-L200

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ReciprocityMap
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_IsoCyclic
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
  {D : ClassFieldData G A}
variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
  (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem GroundTheory.LocalField.Abstract.ClassFieldData.reciprocity_frobenius_of_unramified (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1)
    {π : fixedModule A (K : Subgroup G)} (hπ : D.valuation K π = Multiplicative.ofAdd 1) :
    D.reciprocity hLK hax (φ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      (π : tateZero A (K : Subgroup G) (L : Subgroup G)) := by sorry
