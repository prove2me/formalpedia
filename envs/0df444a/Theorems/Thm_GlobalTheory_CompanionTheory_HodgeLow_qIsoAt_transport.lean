-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeLow_qIsoAt_transport
-- name    : GlobalTheory.CompanionTheory.HodgeLow.qIsoAt_transport
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:23:57.988804+00:00
-- url     : https://prove2.me/theorems/101b17ea-17cc-4f94-af4e-49eca2c0bae3
-- title:
--   Hodge Low: q Iso At transport
-- statement:
--   The Hodge Low construction uses the q Iso At transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PullbackZeroCochainsAlgebraMap.lean#L13-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PullbackZeroCochainsAlgebraMap.lean#L13-L40

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PullbackZeroCochainsAlgebraMap
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeLow

theorem GlobalTheory.CompanionTheory.HodgeLow.qIsoAt_transport {R A₀ A₁ A₂ B₀ B₁ B₂ A₀' A₁' A₂' B₀' B₁' B₂' : Type} [CommRing R]
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
    [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [AddCommGroup A₀'] [AddCommGroup A₁'] [AddCommGroup A₂']
    [AddCommGroup B₀'] [AddCommGroup B₁'] [AddCommGroup B₂']
    [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀] [Module R B₁] [Module R B₂]
    [Module R A₀'] [Module R A₁'] [Module R A₂'] [Module R B₀'] [Module R B₁'] [Module R B₂']
    {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂} {f : A₁ →ₗ[R] B₁}
    {a₀' : A₀' →ₗ[R] A₁'} {a₁' : A₁' →ₗ[R] A₂'} {b₀' : B₀' →ₗ[R] B₁'} {b₁' : B₁' →ₗ[R] B₂'}
    {f' : A₁' →ₗ[R] B₁'}
    (ea₀ : A₀ ≃ₗ[R] A₀') (ea₁ : A₁ ≃ₗ[R] A₁') (ea₂ : A₂ ≃ₗ[R] A₂')
    (eb₀ : B₀ ≃ₗ[R] B₀') (eb₁ : B₁ ≃ₗ[R] B₁') (eb₂ : B₂ ≃ₗ[R] B₂')
    (ha₀ : ∀ x, ea₁ (a₀ x) = a₀' (ea₀ x)) (ha₁ : ∀ x, ea₂ (a₁ x) = a₁' (ea₁ x))
    (hb₀ : ∀ x, eb₁ (b₀ x) = b₀' (eb₀ x)) (hb₁ : ∀ x, eb₂ (b₁ x) = b₁' (eb₁ x))
    (hf : ∀ x, eb₁ (f x) = f' (ea₁ x)) (h : QIsoAt a₀ a₁ b₀ b₁ f) :
    QIsoAt a₀' a₁' b₀' b₁' f' := by sorry
