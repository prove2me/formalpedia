-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_eq_on_cellDoubleCoset
-- name    : GroundTheory.Automorphic.Parabolic.eq_on_cellDoubleCoset
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:58:45.212592+00:00
-- url     : https://prove2.me/theorems/f9e4c04f-978e-58ea-976e-9134b32da8c4
-- title:
--   Parabolic: eq on cell Double Coset
-- statement:
--   The Parabolic construction uses the eq on cell Double Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L560-L576
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean#L560-L576

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

theorem GroundTheory.Automorphic.Parabolic.eq_on_cellDoubleCoset {J : ℕ}
    {ψ₁ ψ₂ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)}
    (h₁ : ψ₁ ∈ indSpace (cellLeviSub F β γ w) (cellInducing β γ w σ))
    (h₂ : ψ₂ ∈ indSpace (cellLeviSub F β γ w) (cellInducing β γ w σ))
    {s : levi F n γ}
    (hs : ∀ k : levi F n γ, (k : GL (Fin n) F) ∈ congruenceSubgroup F n J → ψ₁ (s * k) = ψ₂ (s * k))
    {m : levi F n γ}
    (hm : ∃ b ∈ cellLeviParabolic F β γ w, ∃ k ∈ levi F n γ ⊓ congruenceSubgroup F n J,
      (m : GL (Fin n) F) = b * s * k) : ψ₁ m = ψ₂ m := by sorry
