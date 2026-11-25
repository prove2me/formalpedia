-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_liftAlong_pull1
-- name    : GlobalTheory.CompanionTheory.HopfSys.liftAlong_pull1
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:06.569547+00:00
-- url     : https://prove2.me/theorems/b9c22ad7-8305-410f-b56f-c14ed7e82566
-- title:
--   Hopf Sys: lift Along pull1
-- statement:
--   The Hopf Sys construction uses the lift Along pull1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechTripleRestrictCompositeInjectiveCohomologyFo.lean#L242-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechTripleRestrictCompositeInjectiveCohomologyFo.lean#L242-L257

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
variable {R : Type} [CommRing R] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ : X' ⟶ X}
  {C D : Type} [Category.{0} C] [Category.{0} D]

theorem GlobalTheory.CompanionTheory.HopfSys.liftAlong_pull1 (h : φ ≫ s = s' ≫ spMap (RingHom.id R)) (u : C ⥤ AffOp X) (t : D ⥤ C)
    (fb : D ⥤ AffOp X') (hle : ∀ d, (fb.obj d).unop.1 ≤ φ ⁻¹ᵁ (u.obj (t.obj d)).unop.1) (c : HO1 s) :
    (liftAlong h u t fb hle).pull1 ((CoefMap.restrict (OAff s) u).pull1 c) =
      (CoefMap.restrict (OAff s') fb).pull1 (pullHO1 h c) := by sorry
