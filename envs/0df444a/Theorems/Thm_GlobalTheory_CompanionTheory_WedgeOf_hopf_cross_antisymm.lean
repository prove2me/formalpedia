-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_hopf_cross_antisymm
-- name    : GlobalTheory.CompanionTheory.WedgeOf.hopf_cross_antisymm
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:33:03.383886+00:00
-- url     : https://prove2.me/theorems/cff1a7b3-e54a-4cf0-aea5-b36fb791527b
-- title:
--   Wedge Of: hopf cross antisymm
-- statement:
--   The Wedge Of construction uses the hopf cross antisymm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CupVanishingAntisymmetricCross.lean#L50-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CupVanishingAntisymmetricCross.lean#L50-L61

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CupVanishingAntisymmetricCross
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_cup

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf

theorem GlobalTheory.CompanionTheory.WedgeOf.hopf_cross_antisymm : LowSt → ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R), Hopf F False → ∀ t : H1 F ⊗[R] H1 F,
    TensorProduct.lift (cup F) t = 0 →
      TensorProduct.lift (crossB F) (t - TensorProduct.comm R _ _ t) = 0 := by sorry
