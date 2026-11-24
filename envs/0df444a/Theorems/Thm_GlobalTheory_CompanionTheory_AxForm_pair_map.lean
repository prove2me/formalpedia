-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_pair_map
-- name    : GlobalTheory.CompanionTheory.AxForm.pair_map
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:23:25.722799+00:00
-- url     : https://prove2.me/theorems/44f80bc6-8659-4c23-8de2-47b423ddeebb
-- title:
--   Ax Form: pair map
-- statement:
--   The Ax Form construction uses the pair map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ModuleHomCompSquareZeroSection.lean#L77-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ModuleHomCompSquareZeroSection.lean#L77-L85

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
variable {R S S' B M N : Type} [CommRing R] [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S'] [CommRing B]
  [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
  [AddCommGroup N] [Module B N] [Module Bᵐᵒᵖ N] [IsCentralScalar B N]

theorem GlobalTheory.CompanionTheory.AxForm.pair_map (u : M →ₗ[B] N) (t : S →+* TrivSqZeroExt B M) (ht : OverR R t)
    (ht' : OverR R ((TrivSqZeroExt.map u).toRingHom.comp t)) (ω : Ω[S⁄R]) :
    pair ((TrivSqZeroExt.map u).toRingHom.comp t) ht' ω = u (pair t ht ω) := by sorry
