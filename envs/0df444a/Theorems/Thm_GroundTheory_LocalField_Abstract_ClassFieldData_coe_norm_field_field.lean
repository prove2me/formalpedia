-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_coe_norm_field_field
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.coe_norm_field_field
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:16:27.81289+00:00
-- url     : https://prove2.me/theorems/362150ae-8de1-4831-b59e-5173fb674bfa
-- title:
--   Class Field Data: coe norm field field
-- statement:
--   The Class Field Data construction uses the coe norm field field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L156-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean#L156-L193

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

theorem GroundTheory.LocalField.Abstract.ClassFieldData.coe_norm_field_field (s1 s2 : D.FrobeniusLift K) (k : ℕ) (hk : 0 < k)
    (h2 : s2.elt = s1.elt ^ k) (hdeg : s2.deg = k * s1.deg)
    (z : fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G)) :
    (norm A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)
      ((s2.field L hLK : OpenSubgroup G) : Subgroup G) z : A) =
      ∏ i : Fin k, s1.elt ^ (i : ℕ) • (z : A) := by sorry
