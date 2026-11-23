-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_le_rightStab_avgOver
-- name    : GroundTheory.Automorphic.Parabolic.le_rightStab_avgOver
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:38.681728+00:00
-- url     : https://prove2.me/theorems/d7fb3e87-c5f9-4ce6-b9e1-ee3242236a79
-- title:
--   Parabolic: le right Stab avg Over
-- statement:
--   The Parabolic construction uses the le right Stab avg Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L126-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L126-L127

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Set
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
variable {K : Subgroup G} {f : G → W}

theorem GroundTheory.Automorphic.Parabolic.le_rightStab_avgOver (hf : AvgFinite K f) : K ≤ rightStab (avgOver K f) := by sorry
