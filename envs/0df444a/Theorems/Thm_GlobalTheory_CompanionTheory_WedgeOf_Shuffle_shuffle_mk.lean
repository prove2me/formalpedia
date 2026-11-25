-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_Shuffle_shuffle_mk
-- name    : GlobalTheory.CompanionTheory.WedgeOf.Shuffle.shuffle_mk
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:58:28.735805+00:00
-- url     : https://prove2.me/theorems/5e9e717a-f234-494e-b0c0-f60adc8b0e68
-- title:
--   Shuffle: shuffle mk
-- statement:
--   The Shuffle construction uses the shuffle mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CrossProductKernelQuotientVanishing.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CrossProductKernelQuotientVanishing.lean#L78-L80

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

theorem GlobalTheory.CompanionTheory.WedgeOf.Shuffle.shuffle_mk (z : C2 (box F)) {a a' b b' : C} (φ : a ⟶ a') (ψ : b ⟶ b') :
    shuffle F z (⟨a, a', φ⟩, ⟨b, b', ψ⟩) =
      z (a, b) (a', b) (a', b') (φ, 𝟙 b) (𝟙 a', ψ) - z (a, b) (a, b') (a', b') (𝟙 a, ψ) (φ, 𝟙 b') := by sorry
