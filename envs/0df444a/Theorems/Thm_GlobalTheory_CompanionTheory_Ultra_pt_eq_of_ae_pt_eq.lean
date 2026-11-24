-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_pt_eq_of_ae_pt_eq
-- name    : GlobalTheory.CompanionTheory.Ultra.pt_eq_of_ae_pt_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:19:46.174023+00:00
-- url     : https://prove2.me/theorems/b9e1a085-f21c-48e5-a389-162b063149a6
-- title:
--   Ultra: pt eq of ae pt eq
-- statement:
--   The Ultra construction uses the pt eq of ae pt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L412-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L412-L454

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteAffineCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ultra
variable {ι : Type} (U : Ultrafilter ι)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X : Scheme.{0}}
variable {A : ι → Type} [∀ i, CommRing (A i)]

theorem GlobalTheory.CompanionTheory.Ultra.pt_eq_of_ae_pt_eq [QuasiSeparatedSpace X] [∀ i, IsLocalRing (A i)]
    {W₁ W₂ : X.affineOpens} {h₁ : ∀ i, Γ(X, W₁.1) → A i} {h₂ : ∀ i, Γ(X, W₂.1) → A i}
    {g₁ : Γ(X, W₁.1) →+* Ult U A} {g₂ : Γ(X, W₂.1) →+* Ult U A}
    (r₁ : Rep U h₁ g₁) (r₂ : Rep U h₂ g₂)
    (H : ∀ᶠ i in (U : Filter ι), ∃ (p : Γ(X, W₁.1) →+* A i) (q : Γ(X, W₂.1) →+* A i),
      ⇑p = h₁ i ∧ ⇑q = h₂ i ∧ pt W₁ p = pt W₂ q) :
    pt W₁ g₁ = pt W₂ g₂ := by sorry
