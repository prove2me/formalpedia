-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_eq_smul_avgOver_inf
-- name    : GroundTheory.Automorphic.Parabolic.avgOver_eq_smul_avgOver_inf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:34.660813+00:00
-- url     : https://prove2.me/theorems/70252e70-7716-428f-ade5-3d89d77ab109
-- title:
--   Parabolic: avg Over eq smul avg Over inf
-- statement:
--   The Parabolic construction uses the avg Over eq smul avg Over inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCount.lean#L84-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCount.lean#L84-L160

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

theorem GroundTheory.Automorphic.Parabolic.avgOver_eq_smul_avgOver_inf {K K' : Subgroup G} {h : G → W} (hKK' : K ≤ K')
    (hf : AvgFinite K h) (hK : K.relIndex K' ≠ 0)
    (hsupp : ∀ y ∈ K', h y ≠ 0 → ∃ a ∈ A, ∃ k ∈ K, y = a * k) :
    avgOver K' h 1 = (((K.relIndex K' : ℂ)⁻¹ * ((K ⊓ A).relIndex (K' ⊓ A) : ℂ))) •
      avgOver (K' ⊓ A) (avgOver K h) 1 := by sorry
