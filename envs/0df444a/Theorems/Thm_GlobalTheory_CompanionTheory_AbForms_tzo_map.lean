-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_tzo_map
-- name    : GlobalTheory.CompanionTheory.AbForms.tzo_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:21:34.425001+00:00
-- url     : https://prove2.me/theorems/9d6e1fd0-0aca-4b90-9637-97a3a2e61b36
-- title:
--   Ab Forms: tzo map
-- statement:
--   The Ab Forms construction uses the tzo map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UOfIsBaseChange.lean#L182-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UOfIsBaseChange.lean#L182-L192

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UOfIsBaseChange
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp

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
variable {A : Over (Sp R)} [GrpObj A] {W : Type} [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W]
  [IsCentralScalar R W] {y₀ : Sp (TrivSqZeroExt R W) ⟶ A.left} (hy : IsCot A.hom η[A].left W y₀)
variable {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M] [Module R M] [IsScalarTower R B M]
variable {B' M' : Type} [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M']
  [IsCentralScalar B' M'] [Module R M'] [IsScalarTower R B' M']

theorem GlobalTheory.CompanionTheory.AbForms.tzo_map (α : B →+* B') (hα : α.comp (algebraMap R B) = algebraMap R B') (f : M →ₗ[R] M')
    (hf : ∀ b m, (f : M →+ M') (b • m) = α b • (f : M →+ M') m)
    (h : (tmap α (f : M →+ M') hf).comp (sz (R := R) B M) = sz B' M') (u : W →ₗ[R] M) :
    spo (tmap α (f : M →+ M') hf) h ≫ tzo hy u = tzo (B := B') hy (f ∘ₗ u) := by sorry
