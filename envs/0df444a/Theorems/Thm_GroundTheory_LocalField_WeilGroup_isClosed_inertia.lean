-- Prove2me | Theorems.Thm_GroundTheory_LocalField_WeilGroup_isClosed_inertia
-- name    : GroundTheory.LocalField.WeilGroup.isClosed_inertia
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:06:47.0214+00:00
-- url     : https://prove2.me/theorems/56e93d78-eca7-584e-b312-bec64a3daca8
-- title:
--   Weil Group: is Closed inertia
-- statement:
--   The Weil Group construction uses the is Closed inertia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WeilGroupDefs.lean#L240-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WeilGroupDefs.lean#L240-L241

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
variable {K Ω}

theorem GroundTheory.LocalField.WeilGroup.isClosed_inertia : IsClosed (inertia K Ω : Set (WeilGroup K Ω)) := by sorry
