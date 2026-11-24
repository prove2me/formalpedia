-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QCalc_qIsoAt_left
-- name    : GlobalTheory.CompanionTheory.QCalc.qIsoAt_left
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:26:39.880521+00:00
-- url     : https://prove2.me/theorems/82b23df4-761a-492d-b4a9-2c320ea1c902
-- title:
--   QCalc: q Iso At left
-- statement:
--   The QCalc construction uses the q Iso At left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QIsoAtRight.lean#L54-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QIsoAtRight.lean#L54-L65

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QIsoAtRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QCalc
variable {R A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ C₂ : Type} [CommRing R]
  [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
  [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
  [AddCommGroup C₀] [AddCommGroup C₁] [AddCommGroup C₂]
  [Module R A₀] [Module R A₁] [Module R A₂]
  [Module R B₀] [Module R B₁] [Module R B₂]
  [Module R C₀] [Module R C₁] [Module R C₂]
  {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂}
  {c₀ : C₀ →ₗ[R] C₁} {c₁ : C₁ →ₗ[R] C₂}
  {f₀ : A₀ →ₗ[R] B₀} {f₁ : A₁ →ₗ[R] B₁} {f₂ : A₂ →ₗ[R] B₂}
  {g₀ : B₀ →ₗ[R] C₀} {g₁ : B₁ →ₗ[R] C₁} {g₂ : B₂ →ₗ[R] C₂} {k : A₁ →ₗ[R] C₁}

theorem GlobalTheory.CompanionTheory.QCalc.qIsoAt_left (hf₂ : ∀ x, f₂ (a₁ x) = b₁ (f₁ x))
    (hg₀ : ∀ x, g₁ (b₀ x) = c₀ (g₀ x)) (hg₂ : ∀ x, g₂ (b₁ x) = c₁ (g₁ x))
    (hk : ∀ x, k x = g₁ (f₁ x))
    (hg : QIsoAt b₀ b₁ c₀ c₁ g₁) (hK : QIsoAt a₀ a₁ c₀ c₁ k) :
    QIsoAt a₀ a₁ b₀ b₁ f₁ := by sorry
