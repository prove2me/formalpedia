-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_qMap_pull1
-- name    : GlobalTheory.CompanionTheory.HopfSys.qMap_pull1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:27.072803+00:00
-- url     : https://prove2.me/theorems/9e17f681-d9d8-42af-b62a-ea83aababa20
-- title:
--   Hopf Sys: q Map pull1
-- statement:
--   The Hopf Sys construction uses the q Map pull1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechTripleRestrictCompositeInjectiveCohomologyFo.lean#L446-L453
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechTripleRestrictCompositeInjectiveCohomologyFo.lean#L446-L453

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
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {P : Type} [SemilatticeInf P] (S : Sys A.left P)
  [IsSeparated A.hom]

theorem GlobalTheory.CompanionTheory.HopfSys.qMap_pull1 (x : H1 (OSys A.hom S)) :
    (qMap A S).pull1 x = (pj A S).coef.pull1 ((boxR (OSys A.hom S)).pull1 x) := by sorry
