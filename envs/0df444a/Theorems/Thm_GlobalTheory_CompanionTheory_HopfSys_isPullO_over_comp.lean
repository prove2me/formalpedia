-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_isPullO_over_comp
-- name    : GlobalTheory.CompanionTheory.HopfSys.isPullO_over_comp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:39:20.151823+00:00
-- url     : https://prove2.me/theorems/2db3d1c1-8edd-4e8f-a6a1-4b8b08905f5e
-- title:
--   Hopf Sys: is Pull O over comp
-- statement:
--   The Hopf Sys construction uses the is Pull O over comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechTripleRestrictCompositeInjectiveCohomologyFo.lean#L157-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechTripleRestrictCompositeInjectiveCohomologyFo.lean#L157-L160

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

theorem GlobalTheory.CompanionTheory.HopfSys.isPullO_over_comp {Y Z T : Over (Sp R)} (f : Y ⟶ Z) (g : Z ⟶ T) {a : HO1 T.hom} {a' : HO1 Z.hom}
    {a'' : HO1 Y.hom} (p : IsPullO (wOver g) a a') (p' : IsPullO (wOver f) a' a'') :
    IsPullO (wOver (f ≫ g)) a a'' := by sorry
