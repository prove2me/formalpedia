-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_Shuffle_shuffle_cup
-- name    : GlobalTheory.CompanionTheory.WedgeOf.Shuffle.shuffle_cup
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:59:16.098139+00:00
-- url     : https://prove2.me/theorems/1d001d76-1d08-4c07-bf6a-050bf0b8bcbb
-- title:
--   Shuffle: shuffle cup
-- statement:
--   The Shuffle construction uses the shuffle cup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CrossProductKernelQuotientVanishing.lean#L69-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CrossProductKernelQuotientVanishing.lean#L69-L76

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

theorem GlobalTheory.CompanionTheory.WedgeOf.Shuffle.shuffle_cup (f h : Z1 F) (x : Ar C × Ar C) :
    shuffle F (cupZ (box F) ((boxL F).pullbackOneCocycle f) ((boxR F).pullbackOneCocycle h)).1 x =
      f.1 _ _ x.1.2.2 ⊗ₜ h.1 _ _ x.2.2.2 := by sorry
