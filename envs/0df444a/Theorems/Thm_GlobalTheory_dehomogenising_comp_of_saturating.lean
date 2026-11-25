-- Prove2me | Theorems.Thm_GlobalTheory_dehomogenising_comp_of_saturating
-- name    : GlobalTheory.dehomogenising_comp_of_saturating
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:17:38.087932+00:00
-- url     : https://prove2.me/theorems/be0d680d-38dc-5ca5-bc27-537c078b147a
-- title:
--   Global Theory: dehomogenising comp of saturating
-- statement:
--   The Global Theory construction uses the dehomogenising comp of saturating property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/DehomogenisingCompOfSaturating.lean#L22-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/DehomogenisingCompOfSaturating.lean#L22-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsBaseChangeCokerMatrixMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyBaseChangeGrCubeIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsHomogeneousRangeMulVecLin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyHomLocSingletonEquivQuotSMulTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsNoetherianSubringHomogeneousMatrixFlatChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FlatHomLocOfFlatHomLocSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FiniteGrCechHomology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_DehomogenisingEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsGradedPresentationSaturating
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FiniteQuotSMulTopXSubOneOfChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_DehomogenisingCompOfSaturating
import Theorems.Thm_GlobalTheory_IsGradedMap_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum TensorProduct
noncomputable section
open GlobalTheory

theorem GlobalTheory.dehomogenising_comp_of_saturating {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type}
    [CommRing R] {N : Type} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
    [IsScalarTower R (MvPolynomial ι R) N] (𝒩 : ℤ → Submodule R N) [PolyGradedSMul ι 𝒩]
    [Decomposition 𝒩] {G : Type} [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    (𝒢 : ℤ → Submodule R G) {ψ : N →ₗ[MvPolynomial ι R] G} (hψ : IsGradedMap 𝒩 𝒢 ψ) (i : ι)
    (h₁ : ∀ y, ψ y = 0 → ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0)
    (h₂ : ∀ z : G, ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range ψ)
    {B : Type} [CommRing B] (π : MvPolynomial ι R →+* B) {P : Type} [AddCommGroup P] [Module B P]
    (ε : G →ₛₗ[π] P) (hπ : π (MvPolynomial.X i) = 1) (hε : Function.Surjective ε)
    (hk : ∀ n, ∀ y ∈ 𝒢 n, ε y = 0 → ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0) :
    Function.Surjective (ε.comp ψ) ∧
      ∀ y, ε.comp ψ y = 0 ↔ ∃ w : N, y = (MvPolynomial.X i - 1 : MvPolynomial ι R) • w := by sorry
