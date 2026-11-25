-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_zero_of_le
-- name    : GroundTheory.Automorphic.Parabolic.avgOver_eq_zero_of_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:33:08.302163+00:00
-- url     : https://prove2.me/theorems/5316ca65-22b3-4fce-8e27-33e62677dba5
-- title:
--   Parabolic: avg Over eq zero of le
-- statement:
--   The Parabolic construction uses the avg Over eq zero of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCount.lean#L205-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCount.lean#L205-L215

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
variable {A : Subgroup G}
variable (θ : A → W →ₗ[ℂ] W)

theorem GroundTheory.Automorphic.Parabolic.avgOver_eq_zero_of_le {K K' : Subgroup G} {h : G → W}
    (hh : ∀ a : A, ∀ y, h ((a : G) * y) = θ a (h y)) (hKK' : K ≤ K') (hf : AvgFinite K h)
    (hK : K.relIndex K' ≠ 0) (hsupp : ∀ y ∈ K', h y ≠ 0 → ∃ a ∈ A, ∃ k ∈ K, y = a * k)
    (h0 : avgOver K h 1 = 0) : avgOver K' h 1 = 0 := by sorry
