-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_cellJacquet_bump
-- name    : GroundTheory.Automorphic.Parabolic.exists_cellJacquet_bump
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:04:04.348813+00:00
-- url     : https://prove2.me/theorems/41ed3897-8cf4-53f8-8a56-558ef98cd40f
-- title:
--   Parabolic: exists cell Jacquet bump
-- statement:
--   The Parabolic construction uses the exists cell Jacquet bump property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L306-L474
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L306-L474

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
  (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)
include hYo hCY hYP hYQ

theorem GroundTheory.Automorphic.Parabolic.exists_cellJacquet_bump (J : ℕ) {v : W}
    (hv : ∀ p : blockUpper F n β, (p : GL (Fin n) F) ∈ congruenceSubgroup F n J →
      inflateTwist F n β σ p v = v) :
    ∃ f : parabolicIndSpace F n β σ, ∃ _ : f ∈ supportedIn σ Y,
      (∀ m ∈ levi F n γ, cellJacquet γ w σ f m ≠ 0 →
        ∃ b ∈ cellLeviParabolic F β γ w, ∃ k ∈ levi F n γ ⊓ congruenceSubgroup F n J,
          m = b * k) ∧
      (∀ m, ∀ k ∈ levi F n γ ⊓ congruenceSubgroup F n J,
        cellJacquet γ w σ f (m * k) = cellJacquet γ w σ f m) ∧
      ∃ c : ℂ, c ≠ 0 ∧ cellJacquet γ w σ f 1 = c • Representation.Coinvariants.mk _ v := by sorry
