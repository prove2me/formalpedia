-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_Shuffle_exists_boundary
-- name    : GlobalTheory.CompanionTheory.WedgeOf.Shuffle.exists_boundary
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:58:22.323825+00:00
-- url     : https://prove2.me/theorems/08b9c6bc-c891-5bf2-8405-80fde59e7b3e
-- title:
--   Shuffle: exists boundary
-- statement:
--   The Shuffle construction uses the exists boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CrossProductKernelQuotientVanishing.lean#L174-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CrossProductKernelQuotientVanishing.lean#L174-L187

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
variable (F)

theorem GlobalTheory.CompanionTheory.WedgeOf.Shuffle.exists_boundary [Finite C] [Quiver.IsThin C] (s : Z1 F ⊗[R] Z1 F) (w : C1 (box F))
    (hw : d1 (box F) w = (crossZ F s).1) :
    ∃ (u : C1 F ⊗[R] C0 F) (v : C0 F ⊗[R] C1 F), TensorProduct.map (Z1 F).subtype (Z1 F).subtype s =
      TensorProduct.map (d0 F) LinearMap.id v - TensorProduct.map LinearMap.id (d0 F) u := by sorry
