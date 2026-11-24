-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgFinite_of_isOpen
-- name    : GroundTheory.Automorphic.Parabolic.avgFinite_of_isOpen
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:42:01.755829+00:00
-- url     : https://prove2.me/theorems/64fb2c54-7127-457b-8423-91b9c4118846
-- title:
--   Parabolic: avg Finite of is Open
-- statement:
--   The Parabolic construction uses the avg Finite of is Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L353-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaAverage.lean#L353-L355

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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {W : Type*} [AddCommGroup W] [Module ℂ W]
omit [AddCommGroup W] [Module ℂ W]

theorem GroundTheory.Automorphic.Parabolic.avgFinite_of_isOpen {K U : Subgroup G} {f : G → W} (hK : IsCompact (K : Set G))
    (hU : IsOpen (U : Set G)) (hUf : U ≤ rightStab f) : AvgFinite K f := by sorry
