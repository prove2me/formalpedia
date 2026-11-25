-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_recFrob_mul_ofDegOne
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.recFrob_mul_ofDegOne
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:37:18.454667+00:00
-- url     : https://prove2.me/theorems/97b325a1-c443-4184-b6a9-da313aeffc31
-- title:
--   Class Field Data: rec Frob mul of Deg One
-- statement:
--   The Class Field Data construction uses the rec Frob mul of Deg One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Multiplicative.lean#L107-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Multiplicative.lean#L107-L309

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

theorem GroundTheory.LocalField.Abstract.ClassFieldData.recFrob_mul_ofDegOne (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    (s : D.FrobeniusLift K) {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂)) :
    D.recFrob L hLK (s.mul (FrobeniusLift.ofDegOne hφK hdφ)) =
      D.recFrob L hLK s * D.recFrob L hLK (FrobeniusLift.ofDegOne hφK hdφ) := by sorry
