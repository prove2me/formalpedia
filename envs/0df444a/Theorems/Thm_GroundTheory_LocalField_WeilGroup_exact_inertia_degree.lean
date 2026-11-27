-- Prove2me | Theorems.Thm_GroundTheory_LocalField_WeilGroup_exact_inertia_degree
-- name    : GroundTheory.LocalField.WeilGroup.exact_inertia_degree
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:59:59.034822+00:00
-- url     : https://prove2.me/theorems/23e82a7e-a24f-5e17-b554-ab068831b84d
-- title:
--   Weil Group: exact inertia degree
-- statement:
--   The Weil Group construction uses the exact inertia degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WeilGroupDefs.lean#L198-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WeilGroupDefs.lean#L198-L203

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
variable (K Ω)

theorem GroundTheory.LocalField.WeilGroup.exact_inertia_degree :
    (degree K Ω).ker = inertia K Ω ∧ Function.Surjective (degree K Ω) ∧
      (inertia K Ω).map (toGal K Ω) = (maximalUnramifiedExtension K Ω).fixingSubgroup := by sorry
