-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_bump_mem_range
-- name    : GroundTheory.Automorphic.Parabolic.exists_bump_mem_range
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:04:18.108801+00:00
-- url     : https://prove2.me/theorems/9c3ada90-b0bc-59e7-903a-ca0507b148e1
-- title:
--   Parabolic: exists bump mem range
-- statement:
--   The Parabolic construction uses the exists bump mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L510-L551
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L510-L551

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
  (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)
include hYo hCY hYQ
variable (hYP : ∀ p ∈ blockUpper F n β, ∀ g ∈ Y, p * g ∈ Y)
include hYP

theorem GroundTheory.Automorphic.Parabolic.exists_bump_mem_range (J : ℕ) {v : W}
    (hv : ∀ p : blockUpper F n β, (p : GL (Fin n) F) ∈ congruenceSubgroup F n J →
      inflateTwist F n β σ p v = v)
    {s : GL (Fin n) F} (hs : s ∈ levi F n γ ⊓ integralGL F n) :
    ∃ χ ∈ LinearMap.range (cellJacquetMap γ w σ hYo hCY),
      (∀ m : levi F n γ, (χ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) m ≠ 0 →
        ∃ b ∈ cellLeviParabolic F β γ w, ∃ k ∈ levi F n γ ⊓ congruenceSubgroup F n J,
          (m : GL (Fin n) F) = b * s * k) ∧
      (∀ k : levi F n γ, (k : GL (Fin n) F) ∈ congruenceSubgroup F n J →
        (χ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)) (⟨s, hs.1⟩ * k) = Representation.Coinvariants.mk _ v) := by sorry
