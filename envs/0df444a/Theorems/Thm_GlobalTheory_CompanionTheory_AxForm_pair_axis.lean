-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_pair_axis
-- name    : GlobalTheory.CompanionTheory.AxForm.pair_axis
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:23:46.544746+00:00
-- url     : https://prove2.me/theorems/9e756168-52b5-42a3-a443-3073683ce138
-- title:
--   Ax Form: pair axis
-- statement:
--   The Ax Form construction uses the pair axis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ModuleHomCompSquareZeroSection.lean#L177-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ModuleHomCompSquareZeroSection.lean#L177-L202

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModuleHomCompSquareZeroSection
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp

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
open KaehlerDifferential
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AxForm
variable {R : Type} [CommRing R] {X X' : Scheme.{0}}

theorem GlobalTheory.CompanionTheory.AxForm.pair_axis {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap (RingHom.id R))
    (ω : GlobForm s) (hω : IsPullForm h ω 0) (U : X.affineOpens) {B M : Type} [CommRing B] [Algebra R B]
    [IsLocalRing B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    (t : Sec s U.1 →+* TrivSqZeroExt B M) (ht : OverR R t) (y : Sp (TrivSqZeroExt B M) ⟶ X')
    (hy : y ≫ s' = spMap ((TrivSqZeroExt.inlHom B M).comp (algebraMap R B)))
    (e : spMap t ≫ affPt s U = y ≫ φ) : pair t ht (ω.1 (op U)) = 0 := by sorry
