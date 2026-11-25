-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CotLoc_equiv_of_universal
-- name    : GlobalTheory.CompanionTheory.CotLoc.equiv_of_universal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:57:58.095908+00:00
-- url     : https://prove2.me/theorems/f000ac3e-6a18-45cd-b559-2bbe2cfbd965
-- title:
--   Cot Loc: equiv of universal
-- statement:
--   The Cot Loc construction uses the equiv of universal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CotangentLocalOpenChartExists.lean#L125-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CotangentLocalOpenChartExists.lean#L125-L161

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
variable {N : Type} [AddCommGroup N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N]
  [Module R N] [IsScalarTower R R' N]

theorem GlobalTheory.CompanionTheory.CotLoc.equiv_of_universal (hcot : IsCot s e W y₀) (hes : e ≫ s = 𝟙 _)
    [IsOpenImmersion j] [Mono k]
    (hjs : j ≫ s = spMap (algebraMap C A) ≫ k)
    (hje : spMap (algebraMap A R') ≫ j = spMap (algebraMap R R') ≫ e)
    (iW : W →ₗ[R] N) (ψ₁ : A →+* TrivSqZeroExt R' M) (h₁ : Good (C := C) ψ₁)
    (extW : ∀ u : W →ₗ[R] M, ∃ u' : N →ₗ[R'] M, (u'.restrictScalars R).comp iW = u)
    (extM : ∀ ψ : A →+* TrivSqZeroExt R' N, Good (C := C) ψ →
      ∃ v : M →ₗ[R'] N, (tsz (R := R') (B := R') v).comp ψ₁ = ψ)
    (uniqW : ∀ f g : N →ₗ[R'] N, (f.restrictScalars R).comp iW = (g.restrictScalars R).comp iW → f = g)
    (uniqM : ∀ f g : M →ₗ[R'] M, (tsz (R := R') (B := R') f).comp ψ₁ =
      (tsz (R := R') (B := R') g).comp ψ₁ → f = g) :
    Nonempty (N ≃ₗ[R'] M) := by sorry
