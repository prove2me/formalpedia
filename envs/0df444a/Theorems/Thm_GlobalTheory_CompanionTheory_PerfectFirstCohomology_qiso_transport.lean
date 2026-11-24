-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PerfectFirstCohomology_qiso_transport
-- name    : GlobalTheory.CompanionTheory.PerfectFirstCohomology.qiso_transport
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:02:25.440891+00:00
-- url     : https://prove2.me/theorems/17159d7e-c5a6-450d-b2fd-d6034144299f
-- title:
--   Perfect First Cohomology: qiso transport
-- statement:
--   The Perfect First Cohomology construction uses the qiso transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PerfectFirstCohomologyBaseChange.lean#L136-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PerfectFirstCohomologyBaseChange.lean#L136-L164

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FlatQuotientOfUniversallyInjectiveStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LinearMapZeroOfInjectiveFullRankStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFreeKernelSplittingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalSplittingKernelBaseChangeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelFreeAtPrimesOfConstantRankStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelBaseChangeTowerEquivStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RetractBaseChangeKernelCompatibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuasiIsomorphismDegreeOneKernelStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CochainBaseChangeEquivalencesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UniversalCoefficientDegreeZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelEquivCohomologyOfQuasiIsomorphismStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FirstCohomologyBaseChangeOfCochainEquivsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PerfectFirstCohomologyBaseChange
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PerfectFirstCohomology

theorem GlobalTheory.CompanionTheory.PerfectFirstCohomology.qiso_transport {R S A₀ A₁ A₂ B₀ B₁ B₂ A₀' A₁' A₂' B₀' B₁' B₂' : Type} [CommRing R] [CommRing S]
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀] [Module R B₁] [Module R B₂]
    [AddCommGroup A₀'] [AddCommGroup A₁'] [AddCommGroup A₂'] [AddCommGroup B₀'] [AddCommGroup B₁'] [AddCommGroup B₂']
    [Module S A₀'] [Module S A₁'] [Module S A₂'] [Module S B₀'] [Module S B₁'] [Module S B₂']
    {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂} {f : A₁ →ₗ[R] B₁}
    {a₀' : A₀' →ₗ[S] A₁'} {a₁' : A₁' →ₗ[S] A₂'} {b₀' : B₀' →ₗ[S] B₁'} {b₁' : B₁' →ₗ[S] B₂'} {f' : A₁' →ₗ[S] B₁'}
    (h : QIsoAt a₀ a₁ b₀ b₁ f) (ε₀ : A₀ ≃+ A₀') (ε₁ : A₁ ≃+ A₁') (ε₂ : A₂ ≃+ A₂')
    (η₀ : B₀ ≃+ B₀') (η₁ : B₁ ≃+ B₁') (η₂ : B₂ ≃+ B₂')
    (h0 : ∀ y, a₀' (ε₀ y) = ε₁ (a₀ y)) (h1 : ∀ x, a₁' (ε₁ x) = ε₂ (a₁ x))
    (k0 : ∀ y, b₀' (η₀ y) = η₁ (b₀ y)) (k1 : ∀ x, b₁' (η₁ x) = η₂ (b₁ x))
    (hf : ∀ x, f' (ε₁ x) = η₁ (f x)) : QIsoAt a₀' a₁' b₀' b₁' f' := by sorry
