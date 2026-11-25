-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_characterExtensionRep_apply
-- name    : GlobalTheory.CompanionTheory.HypWedge.characterExtensionRep_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:00:27.056152+00:00
-- url     : https://prove2.me/theorems/eb1fbdf4-d0b8-4317-8275-ff5d4c29a596
-- title:
--   Hyp Wedge: character Extension Rep apply
-- statement:
--   The Hyp Wedge construction uses the character Extension Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FormComponentOfWedgeClassZero.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FormComponentOfWedgeClassZero.lean#L36-L38

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HypWedge
variable {R M N V W : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem GlobalTheory.CompanionTheory.HypWedge.characterExtensionRep_apply (B : M →ₗ[R] M →ₗ[R] N) (h : ∀ x, B x x = 0) (a b : M) :
    ext2 B h (exteriorPower.ιMulti R 2 ![a, b]) = B a b := by sorry
