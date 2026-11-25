-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_Shuffle_shuffle_coboundary_one
-- name    : GlobalTheory.CompanionTheory.WedgeOf.Shuffle.shuffle_coboundary_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:58:35.446831+00:00
-- url     : https://prove2.me/theorems/66dda8ab-ba1f-49a3-a636-496c19a1b0e9
-- title:
--   Shuffle: shuffle coboundary one
-- statement:
--   The Shuffle construction uses the shuffle coboundary one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CrossProductKernelQuotientVanishing.lean#L82-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CrossProductKernelQuotientVanishing.lean#L82-L93

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

theorem GlobalTheory.CompanionTheory.WedgeOf.Shuffle.shuffle_coboundary_one (w : C1 (box F)) {a a' b b' : C} (φ : a ⟶ a') (ψ : b ⟶ b') :
    shuffle F (d1 (box F) w) (⟨a, a', φ⟩, ⟨b, b', ψ⟩) =
      (TensorProduct.map LinearMap.id (mp F ψ).toLinearMap (w (a, b) (a', b) (φ, 𝟙 b)) - w (a, b') (a', b') (φ, 𝟙 b')) +
      (w (a', b) (a', b') (𝟙 a', ψ) -
        TensorProduct.map (mp F φ).toLinearMap LinearMap.id (w (a, b) (a, b') (𝟙 a, ψ))) := by sorry
