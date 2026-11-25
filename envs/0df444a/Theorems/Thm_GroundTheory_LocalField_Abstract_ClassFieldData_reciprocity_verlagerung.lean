-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_reciprocity_verlagerung
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.reciprocity_verlagerung
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:03:38.798959+00:00
-- url     : https://prove2.me/theorems/28e46c26-69ba-5290-ada2-deba993f3cc5
-- title:
--   Class Field Data: reciprocity verlagerung
-- statement:
--   The Class Field Data construction uses the reciprocity verlagerung property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/FunctorialityTransfer.lean#L294-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/FunctorialityTransfer.lean#L294-L402

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityTransfer
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

theorem GroundTheory.LocalField.Abstract.ClassFieldData.reciprocity_verlagerung (hax : ClassFieldAxiom G A) [IsDiscreteModule G A] (hLK' : L ≤ K')
    (hK'K : K' ≤ K) (g : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    Abelianization.lift (D.reciprocity hLK' hax) (verlagerung hK'K g) =
      tateZeroIncl hLK' hK'K (D.reciprocity (hLK'.trans hK'K) hax g) := by sorry
