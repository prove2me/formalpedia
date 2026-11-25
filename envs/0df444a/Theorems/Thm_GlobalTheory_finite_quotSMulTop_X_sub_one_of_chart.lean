-- Prove2me | Theorems.Thm_GlobalTheory_finite_quotSMulTop_X_sub_one_of_chart
-- name    : GlobalTheory.finite_quotSMulTop_X_sub_one_of_chart
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:52:00.587111+00:00
-- url     : https://prove2.me/theorems/e28467df-f4e0-41dd-acba-b3f7e409ee1c
-- title:
--   Global Theory: finite quot SMul Top X sub one of chart
-- statement:
--   The Global Theory construction uses the finite quot SMul Top X sub one of chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FiniteQuotSMulTopXSubOneOfChart.lean#L17-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FiniteQuotSMulTopXSubOneOfChart.lean#L17-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_DehomogenisingEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FiniteQuotSMulTopXSubOneOfChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Pointwise

theorem GlobalTheory.finite_quotSMulTop_X_sub_one_of_chart : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [_root_.GlobalTheory.PolyGradedSMul ι 𝒢]
    [Decomposition 𝒢] (i : ι) (B : Type) (_ : CommRing B) (_ : Algebra R B)
    (π : MvPolynomial ι R →ₐ[R] B) (P : Type) (_ : AddCommGroup P) (_ : Module B P)
    (ε : G →ₛₗ[(π : MvPolynomial ι R →+* B)] P),
    (Function.Surjective π ∧ π (MvPolynomial.X i) = 1 ∧ Function.Surjective ε ∧
      ∀ n, ∀ y ∈ 𝒢 n, ε y = 0 → ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0) →
    (Module.Finite B P → Module.Finite (MvPolynomial ι R)
      (QuotSMulTop ((MvPolynomial.X i : MvPolynomial ι R) - 1) G)) ∧
    (Algebra.FinitePresentation R B → Module.FinitePresentation B P →
      Module.FinitePresentation (MvPolynomial ι R)
        (QuotSMulTop ((MvPolynomial.X i : MvPolynomial ι R) - 1) G)) := by sorry
