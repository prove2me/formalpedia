-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_core
-- name    : GlobalTheory.CompanionTheory.AxForm.core
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:23:02.452515+00:00
-- url     : https://prove2.me/theorems/d413f036-b9dd-469e-a1e2-57647b97f3e8
-- title:
--   Ax Form: core
-- statement:
--   The Ax Form construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ModuleHomCompSquareZeroSection.lean#L313-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ModuleHomCompSquareZeroSection.lean#L313-L371

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
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.AxForm.core (A : Over (Sp R)) [GrpObj A] {B M : Type} [CommRing B] [Algebra R B] [IsLocalRing B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (c : GlobForm (A ⊗ A).hom)
    (h1 : IsPullForm (wOver (lift (𝟙 A) (1 : A ⟶ A))) c 0) (h2 : IsPullForm (wOver (lift (1 : A ⟶ A) (𝟙 A))) c 0)
    (U : (A ⊗ A).left.affineOpens) (ε : Sec (A ⊗ A).hom U.1 →+* B)
    (hε : spMap ε ≫ affPt (A ⊗ A).hom U = (lift (x0 A B) (x0 A B)).left)
    (l : Ω[Sec (A ⊗ A).hom U.1⁄R] →+ M) (hl : ∀ a ω, l (a • ω) = ε a • l ω) : l (c.1 (op U)) = 0 := by sorry
