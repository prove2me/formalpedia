-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_mem_of_fst
-- name    : GlobalTheory.CompanionTheory.AxForm.mem_of_fst
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:25:58.347221+00:00
-- url     : https://prove2.me/theorems/fae3f8ba-e984-44f2-827c-1544ed5621ab
-- title:
--   Ax Form: mem of fst
-- statement:
--   The Ax Form construction uses the mem of fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ModuleHomCompSquareZeroSection.lean#L149-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ModuleHomCompSquareZeroSection.lean#L149-L169

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModuleHomCompSquareZeroSection
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
variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem GlobalTheory.CompanionTheory.AxForm.mem_of_fst {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
    (y : Sp (TrivSqZeroExt B M) ⟶ X) (W : X.Opens)
    (h : ∀ z, (spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ y) z ∈ W) (z : Sp (TrivSqZeroExt B M)) :
    y z ∈ W := by sorry
