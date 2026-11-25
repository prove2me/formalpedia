-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_relDeg_eq_iff
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.relDeg_eq_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:03:51.425332+00:00
-- url     : https://prove2.me/theorems/2591681e-822f-4c6e-ace7-d4dcf07c7fd1
-- title:
--   Class Field Data: rel Deg eq iff
-- statement:
--   The Class Field Data construction uses the rel Deg eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L184-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Valuation.lean#L184-L186

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
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
open GroundTheory.LocalField.Abstract.ClassFieldData
open ProfiniteInteger
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] (D : ClassFieldData G A)

theorem GroundTheory.LocalField.Abstract.ClassFieldData.relDeg_eq_iff (K : OpenSubgroup G) (σ : (K : Subgroup G)) (x : Multiplicative ℤ̂) :
    D.relDeg K σ = x ↔ D.deg σ = x ^ inertiaDegree D.deg K := by sorry
