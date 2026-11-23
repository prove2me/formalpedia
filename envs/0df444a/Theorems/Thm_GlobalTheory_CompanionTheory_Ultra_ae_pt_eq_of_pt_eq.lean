-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ultra_ae_pt_eq_of_pt_eq
-- name    : GlobalTheory.CompanionTheory.Ultra.ae_pt_eq_of_pt_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:03:04.583211+00:00
-- url     : https://prove2.me/theorems/5c4bf163-7ba7-4fd6-938f-f013791f163e
-- title:
--   Ultra: ae pt eq of pt eq
-- statement:
--   The Ultra construction uses the ae pt eq of pt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L370-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteAffineCover.lean#L370-L410

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

theorem GlobalTheory.CompanionTheory.Ultra.ae_pt_eq_of_pt_eq [IsLocalRing (Ult U A)]
    (hfp : ∀ W : X.affineOpens, Algebra.FinitePresentation ℤ Γ(X, W.1))
    {W₁ W₂ : X.affineOpens} {h₁ : ∀ i, Γ(X, W₁.1) → A i} {h₂ : ∀ i, Γ(X, W₂.1) → A i}
    {g₁ : Γ(X, W₁.1) →+* Ult U A} {g₂ : Γ(X, W₂.1) →+* Ult U A}
    (r₁ : Rep U h₁ g₁) (r₂ : Rep U h₂ g₂) (H : pt W₁ g₁ = pt W₂ g₂) :
    ∀ᶠ i in (U : Filter ι), ∀ (p : Γ(X, W₁.1) →+* A i) (q : Γ(X, W₂.1) →+* A i),
      ⇑p = h₁ i → ⇑q = h₂ i → pt W₁ p = pt W₂ q := by sorry
