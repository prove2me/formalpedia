-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_bump_permGL
-- name    : GroundTheory.Automorphic.Parabolic.exists_bump_permGL
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:58:08.712289+00:00
-- url     : https://prove2.me/theorems/8e1b6442-ec54-53d1-920b-cc40825bb94d
-- title:
--   Parabolic: exists bump perm GL
-- statement:
--   The Parabolic construction uses the exists bump perm GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L241-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L241-L289

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
  (hYP : ∀ p ∈ blockUpper F n β, ∀ g ∈ Y, p * g ∈ Y)
include hYo hCY hYP

theorem GroundTheory.Automorphic.Parabolic.exists_bump_permGL (J : ℕ) {v : W}
    (hv : ∀ p : blockUpper F n β, (p : GL (Fin n) F) ∈ congruenceSubgroup F n J →
      inflateTwist F n β σ p v = v) :
    ∃ f : parabolicIndSpace F n β σ, f ∈ supportedIn σ Y ∧
      (f : GL (Fin n) F → W) (permGL F w) = v ∧
      ∀ y ∈ blockUpper F n γ, (f : GL (Fin n) F → W) (permGL F w * y) ≠ 0 →
        ∃ x ∈ blockUpper F n γ, ∃ hx : x ∈ blockUpper F n (β ∘ w),
          ∃ q ∈ blockUpper F n γ, q ∈ congruenceSubgroup F n J ∧ y = x * q ∧
            (f : GL (Fin n) F → W) (permGL F w * y) = cellRep β w σ ⟨x, hx⟩ v := by sorry
