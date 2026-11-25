-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_appLE_chain
-- name    : GlobalTheory.CompanionTheory.HopfSys.appLE_chain
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:34:20.636378+00:00
-- url     : https://prove2.me/theorems/5737c3d8-12bd-4b15-8b53-d66bf7a78d86
-- title:
--   Hopf Sys: app LE chain
-- statement:
--   The Hopf Sys construction uses the app LE chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechTripleRestrictCompositeInjectiveCohomologyFo.lean#L476-L480
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechTripleRestrictCompositeInjectiveCohomologyFo.lean#L476-L480

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

theorem GlobalTheory.CompanionTheory.HopfSys.appLE_chain {X Y Z : Scheme.{0}} (ψ : X ⟶ Y) (φ : Y ⟶ Z) (χ : X ⟶ Z) (hχ : ψ ≫ φ = χ) {U : Z.Opens}
    {V : Y.Opens} {W : X.Opens} (e1 : V ≤ φ ⁻¹ᵁ U) (e2 : W ≤ ψ ⁻¹ᵁ V) (e3 : W ≤ χ ⁻¹ᵁ U) (x : Γ(Z, U)) :
    (ψ.appLE V W e2).hom ((φ.appLE U V e1).hom x) = (χ.appLE U W e3).hom x := by sorry
