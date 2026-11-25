-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_Shuffle_phi_left
-- name    : GlobalTheory.CompanionTheory.WedgeOf.Shuffle.phi_left
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:58:44.317068+00:00
-- url     : https://prove2.me/theorems/f024900a-559f-458f-97b7-1b39c5cccce4
-- title:
--   Shuffle: phi left
-- statement:
--   The Shuffle construction uses the phi left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CrossProductKernelQuotientVanishing.lean#L132-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CrossProductKernelQuotientVanishing.lean#L132-L145

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

theorem GlobalTheory.CompanionTheory.WedgeOf.Shuffle.phi_left (Φ : C1 F ⊗[R] C1 F ≃ₗ[R] E F)
    (hΦ : ∀ f g x, Φ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g _ _ x.2.2.2)
    (Φ₂ : C0 F ⊗[R] C1 F ≃ₗ[R] ∀ x : C × Ar C, F.obj x.1 ⊗[R] F.obj x.2.2.1)
    (hΦ₂ : ∀ f g x, Φ₂ (f ⊗ₜ g) x = f x.1 ⊗ₜ g _ _ x.2.2.2) (v : C0 F ⊗[R] C1 F) (x y : Ar C) :
    Φ (TensorProduct.map (d0 F) LinearMap.id v) (x, y) =
      Φ₂ v (x.2.1, y) - TensorProduct.map (mp F x.2.2).toLinearMap LinearMap.id (Φ₂ v (x.1, y)) := by sorry
