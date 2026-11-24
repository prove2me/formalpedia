-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeLow_stein_iff
-- name    : GlobalTheory.CompanionTheory.HodgeLow.stein_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:25:14.704002+00:00
-- url     : https://prove2.me/theorems/c2fd0887-c71e-4327-96ce-fe37e3975a46
-- title:
--   Hodge Low: stein iff
-- statement:
--   The Hodge Low construction uses the stein iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PullbackZeroCochainsAlgebraMap.lean#L149-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PullbackZeroCochainsAlgebraMap.lean#L149-L180

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

theorem GlobalTheory.CompanionTheory.HodgeLow.stein_iff (m : CoefMap (RingHom.id R) F F')
    (h : QIsoAt (0 : R →ₗ[R] C0 F) (d0 F) (0 : R →ₗ[R] C0 F') (d0 F') (pullbackZeroCochains m)) :
    Stein F ↔ Stein F' := by sorry
