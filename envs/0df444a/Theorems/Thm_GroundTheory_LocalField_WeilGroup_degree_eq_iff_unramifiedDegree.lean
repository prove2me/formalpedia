-- Prove2me | Theorems.Thm_GroundTheory_LocalField_WeilGroup_degree_eq_iff_unramifiedDegree
-- name    : GroundTheory.LocalField.WeilGroup.degree_eq_iff_unramifiedDegree
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:01:26.569849+00:00
-- url     : https://prove2.me/theorems/118a8705-1b37-4ed1-8fe1-fb1a43e059fc
-- title:
--   Weil Group: degree eq iff unramified Degree
-- statement:
--   The Weil Group construction uses the degree eq iff unramified Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WeilGroupDefs.lean#L170-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/WeilGroupDefs.lean#L170-L173

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

theorem GroundTheory.LocalField.WeilGroup.degree_eq_iff_unramifiedDegree (σ : WeilGroup K Ω) (n : ℤ) :
    degree K Ω σ = Multiplicative.ofAdd n ↔
      unramifiedDegree K Ω (toGal K Ω σ) = Multiplicative.ofAdd (n : ℤ̂) := by sorry
