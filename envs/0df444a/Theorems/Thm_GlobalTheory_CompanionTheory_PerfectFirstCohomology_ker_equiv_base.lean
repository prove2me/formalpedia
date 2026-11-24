-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PerfectFirstCohomology_ker_equiv_base
-- name    : GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_equiv_base
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:02:22.414419+00:00
-- url     : https://prove2.me/theorems/974873a5-6120-42cc-82ca-be1ec9f17302
-- title:
--   Perfect First Cohomology: ker equiv base
-- statement:
--   The Perfect First Cohomology construction uses the ker equiv base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PerfectFirstCohomologyBaseChange.lean#L209-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PerfectFirstCohomologyBaseChange.lean#L209-L245

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
variable {R C : Type} [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
  {P₀ P₁ P₂ : Type} [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂]
  (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F)
variable {F a₀ a₁ ψ₀ ψ₁ ψ₂}

theorem GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_equiv_base {k : Type} [CommRing k] [Algebra R k] (G : C ⥤ CommAlgCat.{0} k)
    (E₀ : k ⊗[R] C0 F ≃ₗ[k] C0 G) (E₁ : k ⊗[R] C1 F ≃ₗ[k] C1 G) (E₂ : k ⊗[R] C2 F ≃ₗ[k] C2 G)
    (h01 : ∀ x, E₁ ((d0 F).baseChange k x) = d0 G (E₀ x)) (h12 : ∀ x, E₂ ((d1 F).baseChange k x) = d1 G (E₁ x))
    (c0 : ψ₁ ∘ₗ a₀ = d0 F ∘ₗ ψ₀) (c1 : ψ₂ ∘ₗ a₁ = d1 F ∘ₗ ψ₁)
    (d : (P₁ ⧸ LinearMap.range a₀) →ₗ[R] P₂) (hdπ : d ∘ₗ (LinearMap.range a₀).mkQ = a₁)
    (hq : QIsoAt (a₀.lTensor k) (a₁.lTensor k) ((d0 F).lTensor k) ((d1 F).lTensor k) (ψ₁.lTensor k)) :
    Nonempty (LinearMap.ker (d.baseChange k) ≃ₗ[k] H1 G) := by sorry
