-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_rightStab
-- name    : GroundTheory.Automorphic.Parabolic.mem_rightStab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:52.666963+00:00
-- url     : https://prove2.me/theorems/23785464-8e02-4df5-9ca6-177cf45701fa
-- title:
--   Parabolic: mem right Stab
-- statement:
--   The Parabolic construction uses the mem right Stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L54-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L54-L55

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
omit [AddCommGroup W] [Module ℂ W]

theorem GroundTheory.Automorphic.Parabolic.mem_rightStab {f : G → W} {g : G} : g ∈ rightStab f ↔ ∀ x, f (x * g) = f x := by sorry
