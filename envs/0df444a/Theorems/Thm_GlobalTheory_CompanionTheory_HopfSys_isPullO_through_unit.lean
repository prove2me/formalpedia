-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_isPullO_through_unit
-- name    : GlobalTheory.CompanionTheory.HopfSys.isPullO_through_unit
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:35:02.763554+00:00
-- url     : https://prove2.me/theorems/a7b94ac8-5b65-4e0f-8034-30e3a2bf5791
-- title:
--   Hopf Sys: is Pull O through unit
-- statement:
--   The Hopf Sys construction uses the is Pull O through unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechTripleRestrictCompositeInjectiveCohomologyFo.lean#L175-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechTripleRestrictCompositeInjectiveCohomologyFo.lean#L175-L180

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge Limits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HopfSys
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.HopfSys.isPullO_through_unit {Y Z : Over (Sp R)} (g : Y ⟶ 𝟙_ (Over (Sp R))) (e : 𝟙_ (Over (Sp R)) ⟶ Z)
    (c : HO1 Z.hom) : IsPullO (wOver (g ≫ e)) c 0 := by sorry
