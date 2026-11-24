-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeLow_pullbackZeroCochains_algebraMap
-- name    : GlobalTheory.CompanionTheory.HodgeLow.pullbackZeroCochains_algebraMap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:24:00.768918+00:00
-- url     : https://prove2.me/theorems/9bce3035-da85-440f-bf57-c712f6e2b8f0
-- title:
--   Hodge Low: pullback Zero Cochains algebra Map
-- statement:
--   The Hodge Low construction uses the pullback Zero Cochains algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PullbackZeroCochainsAlgebraMap.lean#L130-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PullbackZeroCochainsAlgebraMap.lean#L130-L135

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PullbackZeroCochainsAlgebraMap
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeLow
variable {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R}

theorem GlobalTheory.CompanionTheory.HodgeLow.pullbackZeroCochains_algebraMap (m : CoefMap (RingHom.id R) F F') (r : R) :
    pullbackZeroCochains m (algebraMap R (C0 F) r) = algebraMap R (C0 F') r := by sorry
