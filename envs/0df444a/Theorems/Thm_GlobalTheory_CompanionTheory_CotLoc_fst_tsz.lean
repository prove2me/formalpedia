-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_fst_tsz
-- name    : GlobalTheory.CompanionTheory.CotLoc.fst_tsz
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:58:02.499827+00:00
-- url     : https://prove2.me/theorems/cc953d17-d2f9-4a5c-a43a-056258b02afa
-- title:
--   Cot Loc: fst tsz
-- statement:
--   The Cot Loc construction uses the fst tsz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CotangentLocalOpenChartExists.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CotangentLocalOpenChartExists.lean#L66-L69

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CotangentLocalOpenChartExists
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CotLoc
variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} {e : Sp R ⟶ X}
  {W : Type} [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W] [IsCentralScalar R W]
  {y₀ : Sp (TrivSqZeroExt R W) ⟶ X}
  {R' : Type} [CommRing R'] [Algebra R R'] {A C : Type} [CommRing A] [CommRing C] [Algebra C A]
  [Algebra A R'] {j : Sp A ⟶ X} {k : Sp C ⟶ Sp R}
variable {M : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
  [Module R M] [IsScalarTower R R' M]

theorem GlobalTheory.CompanionTheory.CotLoc.fst_tsz (u : W →ₗ[R] M) :
    (TrivSqZeroExt.fstHom R' R' M).toRingHom.comp (tsz u) =
      (algebraMap R R').comp (TrivSqZeroExt.fstHom R R W).toRingHom := by sorry
