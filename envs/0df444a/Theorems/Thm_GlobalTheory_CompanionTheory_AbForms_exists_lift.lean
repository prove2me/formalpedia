-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_exists_lift
-- name    : GlobalTheory.CompanionTheory.AbForms.exists_lift
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:22:09.394682+00:00
-- url     : https://prove2.me/theorems/6b5274e2-7141-40e8-bb22-40937fe43410
-- title:
--   Ab Forms: exists lift
-- statement:
--   The Ab Forms construction uses the exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UOfIsBaseChange.lean#L50-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UOfIsBaseChange.lean#L50-L71

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UOfIsBaseChange
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AbForms
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.AbForms.exists_lift {X : Scheme.{0}} {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
    [IsCentralScalar B M] (x : Sp B ⟶ X) [IsOpenImmersion x] (y : Sp (TrivSqZeroExt B M) ⟶ X)
    (h : spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ y = x) :
    ∃ σ : B →+* TrivSqZeroExt B M, y = spMap σ ≫ x := by sorry
