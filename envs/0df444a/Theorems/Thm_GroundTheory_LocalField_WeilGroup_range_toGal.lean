-- Prove2me | Theorems.Thm_GroundTheory_LocalField_WeilGroup_range_toGal
-- name    : GroundTheory.LocalField.WeilGroup.range_toGal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:04:07.827906+00:00
-- url     : https://prove2.me/theorems/528780dc-c3d9-445e-ac83-42e9ab11d94f
-- title:
--   Weil Group: range to Gal
-- statement:
--   The Weil Group construction uses the range to Gal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WeilGroupDefs.lean#L124-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WeilGroupDefs.lean#L124-L124

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_WeilGroupDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IntermediateField GroundTheory.LocalField.Abstract Topology
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
open GroundTheory.LocalField.WeilGroup

theorem GroundTheory.LocalField.WeilGroup.range_toGal : (toGal K Ω).range = weilSubgroup K Ω := by sorry
