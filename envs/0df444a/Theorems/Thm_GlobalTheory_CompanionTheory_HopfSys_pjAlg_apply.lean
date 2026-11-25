-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_pjAlg_apply
-- name    : GlobalTheory.CompanionTheory.HopfSys.pjAlg_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:43.289188+00:00
-- url     : https://prove2.me/theorems/a4609d7e-7d4c-444f-820d-5b12fe6a9e09
-- title:
--   Hopf Sys: pj Alg apply
-- statement:
--   The Hopf Sys construction uses the pj Alg apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechTripleRestrictCompositeInjectiveCohomologyFo.lean#L374-L391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechTripleRestrictCompositeInjectiveCohomologyFo.lean#L374-L391

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
variable [IsSeparated A.hom]

theorem GlobalTheory.CompanionTheory.HopfSys.pjAlg_apply (T : (Pᵒᵖ × Pᵒᵖ) × Pᵒᵖ)
    (z : (OSys A.hom S).obj T.1.1 ⊗[R] (OSys A.hom S).obj T.1.2) :
    pjAlg A S T z = Sec.res (A ⊗ A).hom
      (inf_le_left : Wop A S T.1.1.unop T.1.2.unop T.2.unop ≤ Vop A S T.1.1.unop T.1.2.unop)
      (kap A S T.1.1.unop T.1.2.unop z) := by sorry
