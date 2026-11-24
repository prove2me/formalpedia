-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_par_of_family
-- name    : GlobalTheory.CompanionTheory.AbForms.par_of_family
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:25:08.030804+00:00
-- url     : https://prove2.me/theorems/04be517a-efd8-45de-ba83-b1e6e80754d2
-- title:
--   Ab Forms: par of family
-- statement:
--   The Ab Forms construction uses the par of family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UOfIsBaseChange.lean#L362-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UOfIsBaseChange.lean#L362-L431

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UOfIsBaseChange
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AbForms
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
variable {R : Type} [CommRing R]
variable {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem GlobalTheory.CompanionTheory.AbForms.par_of_family (hS : Stein F) {W : Type} [AddCommGroup W] [Module R W] (g : ℕ) (hW : VB R W g)
    (u : ∀ T, W →ₗ[R] Ω[F.obj T⁄R]) (hu : ∀ T, IsBaseChange (F.obj T) (u T))
    (hc : ∀ ⦃T T' : C⦄ (φ : T ⟶ T') (w : W), u T' w = p1 F φ (u T w)) :
    Par F ∧ VB R (Glob1 F) g := by sorry
