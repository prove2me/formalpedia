-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_factor_over
-- name    : GlobalTheory.CompanionTheory.AxForm.factor_over
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:22:41.942613+00:00
-- url     : https://prove2.me/theorems/7b86a5ad-e5cd-4a62-8b42-c9058a25ff88
-- title:
--   Ax Form: factor over
-- statement:
--   The Ax Form construction uses the factor over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ModuleHomCompSquareZeroSection.lean#L137-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ModuleHomCompSquareZeroSection.lean#L137-L141

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
variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem GlobalTheory.CompanionTheory.AxForm.factor_over (s : X ⟶ Sp R) (U : X.affineOpens) {C : Type} [CommRing C] (t : Sec s U.1 →+* C)
    (ρ : R →+* C) (h : (spMap t ≫ affPt s U) ≫ s = spMap ρ) : t.comp (algebraMap R (Sec s U.1)) = ρ := by sorry
