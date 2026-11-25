-- Prove2me | Theorems.Thm_GlobalTheory_homLoc_grSum_res
-- name    : GlobalTheory.homLoc_grSum_res
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:56:22.972966+00:00
-- url     : https://prove2.me/theorems/2952ad11-d6eb-407d-ab16-5dbd69a2c903
-- title:
--   Global Theory: hom Loc gr Sum res
-- statement:
--   The Global Theory construction uses the hom Loc gr Sum res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsHomLocBijectiveGrSum.lean#L111-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsHomLocBijectiveGrSum.lean#L111-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsHomLocBijectiveGrSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory DirectSum MvPolynomial
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type} {R : Type} [CommRing R]

theorem GlobalTheory.homLoc_grSum_res
    {M : Type} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ]
    {A : ℤ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x)
    {B : ℤ → Type} [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
    {y : ι → ∀ n, B n →ₗ[R] B (n + 1)} (hy : OperatorsCommute y)
    (r : ∀ n, A n →ₗ[R] B n) (hr : ∀ i n a, r (n + 1) (x i n a) = y i n (r n a))
    {f : M →ₗ[MvPolynomial ι R] GrSum hx} (hf : IsGradedMap ℳ (GrSum.grading hx) f)
    {g : M →ₗ[MvPolynomial ι R] GrSum hy}
    (hfg : ∀ n m a, f m = GrSum.of hx n a → g m = GrSum.of hy n (r n a))
    {s t : Finset ι} (h : s ⊆ t) (hb : ∀ i ∈ t, ∀ n, Function.Bijective (y i n)) {n : ℤ}
    (z : homLoc ℳ s n) (a : A n) (b : B n)
    (ha : ∀ (k : ℕ) (m : M), awayFrac M (xProd R s) k m = z →
      xProd R s ^ k • GrSum.of hx n a = f m)
    (hb' : ∀ (k : ℕ) (m : M), awayFrac M (xProd R t) k m = homLocRes ℳ h n z →
      xProd R t ^ k • GrSum.of hy n b = g m) : b = r n a := by sorry
