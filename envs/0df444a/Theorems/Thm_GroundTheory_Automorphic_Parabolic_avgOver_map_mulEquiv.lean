-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_map_mulEquiv
-- name    : GroundTheory.Automorphic.Parabolic.avgOver_map_mulEquiv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:41:44.217304+00:00
-- url     : https://prove2.me/theorems/24aec93a-a359-40c8-8d71-aa71f8ae01db
-- title:
--   Parabolic: avg Over map mul Equiv
-- statement:
--   The Parabolic construction uses the avg Over map mul Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCount.lean#L223-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCount.lean#L223-L270

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCount
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

theorem GroundTheory.Automorphic.Parabolic.avgOver_map_mulEquiv (φ : G ≃* G) {K : Subgroup G} {f : G → W} (hf : AvgFinite K f)
    (x : G) :
    avgOver (K.map φ.toMonoidHom) (fun y => f (φ.symm y)) x = avgOver K f (φ.symm x) := by sorry
