-- Prove2me | Theorems.Thm_GlobalTheory_exists_noetherian_model_grCube
-- name    : GlobalTheory.exists_noetherian_model_grCube
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:19:22.709065+00:00
-- url     : https://prove2.me/theorems/7dbd2bfe-11c2-576d-ac66-872fe9ca1182
-- title:
--   Global Theory: exists noetherian model gr Cube
-- statement:
--   The Global Theory construction uses the exists noetherian model gr Cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/DehomogenisingCompOfSaturating.lean#L44-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/DehomogenisingCompOfSaturating.lean#L44-L114

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

theorem GlobalTheory.exists_noetherian_model_grCube (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢]
    [Decomposition 𝒢]
    (H : ∀ i : ι, ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B)
      (π : MvPolynomial ι R →ₐ[R] B) (P : Type) (_ : AddCommGroup P) (_ : Module B P)
      (ε : G →ₛₗ[(π : MvPolynomial ι R →+* B)] P),
      Algebra.Smooth R B ∧ Module.FinitePresentation B P ∧ Module.Projective B P ∧
        Function.Surjective π ∧ π (MvPolynomial.X i) = 1 ∧ Function.Surjective ε ∧
        ∀ n, ∀ y ∈ 𝒢 n, ε y = 0 →
          ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0) :
    ∃ (R₀ : Subring R) (_ : IsNoetherianRing R₀) (C₀ : Cube.{0} ι R₀)
      (θ : Cube.baseChange R C₀ ⟶ grCube ι 𝒢 0),
      (∀ I : Finset ι, I.Nonempty → Module.Flat R₀ (C₀.obj I)) ∧
        (∀ p, Module.Finite R₀ ((cechComplex C₀).homology p)) ∧
        ∀ I : Finset ι, I.Nonempty → Function.Bijective (θ.app I).hom := by sorry
