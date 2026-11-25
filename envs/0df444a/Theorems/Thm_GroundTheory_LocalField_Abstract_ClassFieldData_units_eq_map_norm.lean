-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_units_eq_map_norm
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.units_eq_map_norm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:14:13.696986+00:00
-- url     : https://prove2.me/theorems/9633d786-0437-4a65-ba2b-02720e4cb414
-- title:
--   Class Field Data: units eq map norm
-- statement:
--   The Class Field Data construction uses the units eq map norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Unramified.lean#L182-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Unramified.lean#L182-L200

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Unramified
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
variable {K L : OpenSubgroup G}

theorem GroundTheory.LocalField.Abstract.ClassFieldData.units_eq_map_norm (hax : ClassFieldAxiom G A) (hLK : L ≤ K)
    (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L) :
    D.units K = (D.units L).map (norm A (K : Subgroup G) (L : Subgroup G)) := by sorry
