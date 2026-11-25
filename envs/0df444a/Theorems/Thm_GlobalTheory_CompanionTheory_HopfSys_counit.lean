-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_counit
-- name    : GlobalTheory.CompanionTheory.HopfSys.counit
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:36:38.469349+00:00
-- url     : https://prove2.me/theorems/cad8c680-0bcf-4f69-a13a-de9db9bd7d39
-- title:
--   Hopf Sys: counit
-- statement:
--   The Hopf Sys construction uses the counit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechTripleRestrictCompositeInjectiveCohomologyFo.lean#L597-L616
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechTripleRestrictCompositeInjectiveCohomologyFo.lean#L597-L616

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
variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {P : Type} [SemilatticeInf P] {S : Sys A.left P}
  [IsSeparated A.hom] {a₀ : P}
attribute [local instance] unit_isAffine

theorem GlobalTheory.CompanionTheory.HopfSys.counit (ha : η[A].left ⁻¹ᵁ (S.u a₀).1 = ⊤) (y : H2 (OSys A.hom S)) (w : H2 (box (OSys A.hom S)))
    (e : (pj A S).coef.pull2 w = (mMap A S).pull2 y) :
    (boxE (OSys A.hom S) (op a₀) (epsA ha)).pull2 w = y := by sorry
