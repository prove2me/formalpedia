-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_level_near_permGL
-- name    : GroundTheory.Automorphic.Parabolic.exists_level_near_permGL
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:03:02.110536+00:00
-- url     : https://prove2.me/theorems/89b2a65e-69d1-40a2-8256-32e08fb94494
-- title:
--   Parabolic: exists level near perm GL
-- statement:
--   The Parabolic construction uses the exists level near perm GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L199-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L199-L225

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellSurjective
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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}
variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
include hYo hCY

theorem GroundTheory.Automorphic.Parabolic.exists_level_near_permGL (J : ℕ) :
    ∃ J' ≥ J, ∀ k ∈ congruenceSubgroup F n J', permGL F w * k ∈ Y ∧
      (permGL F w * k ∈ doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
        (blockUpper F n γ) →
      ∃ p ∈ blockUpper F n β, p ∈ congruenceSubgroup F n J ∧
        ∃ q ∈ blockUpper F n γ, q ∈ congruenceSubgroup F n J ∧ permGL F w * k = p * permGL F w * q) := by sorry
