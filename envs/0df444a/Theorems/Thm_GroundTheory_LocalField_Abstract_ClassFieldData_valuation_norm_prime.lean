-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_norm_prime
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.valuation_norm_prime
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:58:32.292033+00:00
-- url     : https://prove2.me/theorems/717d50b4-dc97-5ae4-988d-0f10616ec4bb
-- title:
--   Class Field Data: valuation norm prime
-- statement:
--   The Class Field Data construction uses the valuation norm prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Multiplicative.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Multiplicative.lean#L62-L68

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

theorem GroundTheory.LocalField.Abstract.ClassFieldData.valuation_norm_prime (s : D.FrobeniusLift K)
    {π : fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)}
    (hπ : D.valuation (s.field L hLK) π = Multiplicative.ofAdd 1) :
    D.valuation K (norm A (K : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) π) =
      Multiplicative.ofAdd (s.deg : ℤ̂) := by sorry
