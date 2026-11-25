-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_primitive
-- name    : GlobalTheory.CompanionTheory.HopfSys.primitive
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:31:03.740427+00:00
-- url     : https://prove2.me/theorems/01cc7acc-c2c4-580d-81c7-0deefec6fa36
-- title:
--   Hopf Sys: primitive
-- statement:
--   The Hopf Sys construction uses the primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechTripleRestrictCompositeInjectiveCohomologyFo.lean#L455-L465
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechTripleRestrictCompositeInjectiveCohomologyFo.lean#L455-L465

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

theorem GlobalTheory.CompanionTheory.HopfSys.primitive
    (hAx : ∀ c : HO1 (A ⊗ A).hom, IsPullO (wOver (lift (𝟙 A) (1 : A ⟶ A))) c 0 →
      IsPullO (wOver (lift (1 : A ⟶ A) (𝟙 A))) c 0 → c = 0)
    (hs : Function.Surjective (resSys A.hom S).pull1) (c : H1 (OSys A.hom S)) :
    (mMap A S).pull1 c = (pj A S).coef.pull1 ((boxL (OSys A.hom S)).pull1 c + (boxR (OSys A.hom S)).pull1 c) := by sorry
