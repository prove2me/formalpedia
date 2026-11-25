-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Axis_mp_box_tmul
-- name    : GlobalTheory.CompanionTheory.Axis.mp_box_tmul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:18:16.454593+00:00
-- url     : https://prove2.me/theorems/3cd16d1a-20de-44da-b4ba-00ef02f303d8
-- title:
--   Axis: mp box tmul
-- statement:
--   The Axis construction uses the mp box tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CocycleOnProductFromSecondFactor.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CocycleOnProductFromSecondFactor.lean#L18-L21

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CocycleOnProductFromSecondFactor
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Axis

theorem GlobalTheory.CompanionTheory.Axis.mp_box_tmul {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {a a' b b' : C}
    (φ : a ⟶ a') (ψ : b ⟶ b') (u : F.obj a) (v : F.obj b) :
    mp (box F) (show ((a, b) : C × C) ⟶ (a', b') from (φ, ψ)) (u ⊗ₜ[R] v) = mp F φ u ⊗ₜ[R] mp F ψ v := by sorry
