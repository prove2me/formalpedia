-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_cup_add_cup_swap
-- name    : GlobalTheory.CompanionTheory.WedgeOf.cup_add_cup_swap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:32:47.377901+00:00
-- url     : https://prove2.me/theorems/cfe57b85-e504-4f00-8138-0d90cde346be
-- title:
--   Wedge Of: cup add cup swap
-- statement:
--   The Wedge Of construction uses the cup add cup swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CupVanishingAntisymmetricCross.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CupVanishingAntisymmetricCross.lean#L13-L21

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

theorem GlobalTheory.CompanionTheory.WedgeOf.cup_add_cup_swap {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (a b : H1 F) : cup F a b + cup F b a = 0 := by sorry
