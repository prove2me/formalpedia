-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_map_conj
-- name    : GroundTheory.Automorphic.Parabolic.avgOver_map_conj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T09:45:13.184514+00:00
-- url     : https://prove2.me/theorems/7e0012e2-7170-4b72-a608-18c33f5cd0fb
-- title:
--   Parabolic: avg Over map conj
-- statement:
--   The Parabolic construction uses the avg Over map conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCount.lean#L272-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCount.lean#L272-L277

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

theorem GroundTheory.Automorphic.Parabolic.avgOver_map_conj (b : G) {K : Subgroup G} {f : G → W} (hf : AvgFinite K f) (x : G) :
    avgOver (K.map (MulAut.conj b).toMonoidHom) (fun y => f (b⁻¹ * y * b)) x =
      avgOver K f (b⁻¹ * x * b) := by sorry
