-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_Shuffle_phi_right
-- name    : GlobalTheory.CompanionTheory.WedgeOf.Shuffle.phi_right
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:58:21.958999+00:00
-- url     : https://prove2.me/theorems/e2b3e1d4-8f1e-5309-9800-d70c419432f3
-- title:
--   Shuffle: phi right
-- statement:
--   The Shuffle construction uses the phi right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CrossProductKernelQuotientVanishing.lean#L117-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CrossProductKernelQuotientVanishing.lean#L117-L130

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CrossProductKernelQuotientVanishing
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf GlobalTheory.CompanionTheory.WedgeOf.Shuffle
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}

theorem GlobalTheory.CompanionTheory.WedgeOf.Shuffle.phi_right (Φ : C1 F ⊗[R] C1 F ≃ₗ[R] E F)
    (hΦ : ∀ f g x, Φ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g _ _ x.2.2.2)
    (Φ₁ : C1 F ⊗[R] C0 F ≃ₗ[R] ∀ x : Ar C × C, F.obj x.1.2.1 ⊗[R] F.obj x.2)
    (hΦ₁ : ∀ f g x, Φ₁ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g x.2) (u : C1 F ⊗[R] C0 F) (x y : Ar C) :
    Φ (TensorProduct.map LinearMap.id (d0 F) u) (x, y) =
      Φ₁ u (x, y.2.1) - TensorProduct.map LinearMap.id (mp F y.2.2).toLinearMap (Φ₁ u (x, y.1)) := by sorry
