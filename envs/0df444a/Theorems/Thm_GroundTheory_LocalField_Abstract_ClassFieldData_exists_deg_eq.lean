-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_exists_deg_eq
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.exists_deg_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:00:24.705833+00:00
-- url     : https://prove2.me/theorems/f6090f35-1873-4421-9860-0d96cd328a14
-- title:
--   Class Field Data: exists deg eq
-- statement:
--   The Class Field Data construction uses the exists deg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Multiplicative.lean#L317-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Multiplicative.lean#L317-L321

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

theorem GroundTheory.LocalField.Abstract.ClassFieldData.exists_deg_eq (K : OpenSubgroup G) :
    ∃ φ ∈ (K : Subgroup G), D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂) := by sorry
