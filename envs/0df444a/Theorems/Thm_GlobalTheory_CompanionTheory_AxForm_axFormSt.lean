-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AxForm_axFormSt
-- name    : GlobalTheory.CompanionTheory.AxForm.axFormSt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:03.038566+00:00
-- url     : https://prove2.me/theorems/9c31b85d-166e-5622-8b0e-914ea70e9001
-- title:
--   Ax Form: ax Form St
-- statement:
--   The Ax Form construction uses the ax Form St property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ModuleHomCompSquareZeroSection.lean#L422-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ModuleHomCompSquareZeroSection.lean#L422-L431

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

theorem GlobalTheory.CompanionTheory.AxForm.axFormSt : CotSt → SteinSt → ParSt → AxFormSt := by sorry
