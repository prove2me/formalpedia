-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_stein_holds
-- name    : GlobalTheory.CompanionTheory.Hodge.stein_holds
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:02:51.296774+00:00
-- url     : https://prove2.me/theorems/b1a8118d-41e9-48cb-ad0e-58ed2f61e7ec
-- title:
--   Hodge: stein holds
-- statement:
--   The Hodge construction uses the stein holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SteinOfBijective.lean#L109-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SteinOfBijective.lean#L109-L112

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SteinOfBijective
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge
variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem GlobalTheory.CompanionTheory.Hodge.stein_holds : SteinSt := by sorry
