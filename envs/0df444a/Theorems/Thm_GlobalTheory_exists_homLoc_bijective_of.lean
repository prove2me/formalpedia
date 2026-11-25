-- Prove2me | Theorems.Thm_GlobalTheory_exists_homLoc_bijective_of
-- name    : GlobalTheory.exists_homLoc_bijective_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:58:20.424249+00:00
-- url     : https://prove2.me/theorems/68a01b30-0d25-5eeb-a5ca-34061ff86068
-- title:
--   Global Theory: exists hom Loc bijective of
-- statement:
--   The Global Theory construction uses the exists hom Loc bijective of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsHomLocBijectiveGrSum.lean#L44-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsHomLocBijectiveGrSum.lean#L44-L87

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

theorem GlobalTheory.exists_homLoc_bijective_of
    {M : Type} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    {N : Type} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
    [IsScalarTower R (MvPolynomial ι R) N]
    {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ] [Decomposition ℳ]
    {𝒩 : ℤ → Submodule R N} [PolyGradedSMul ι 𝒩] [Decomposition 𝒩]
    {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (s : Finset ι)
    (hb : Function.Bijective fun m : N => xProd R s • m)
    (h₁ : ∀ n, ∀ y ∈ ℳ n, f y = 0 → ∃ k : ℕ, xProd R s ^ k • y = 0)
    (h₂ : ∀ n, ∀ a ∈ 𝒩 n, ∃ (k : ℕ) (y : M), f y = xProd R s ^ k • a) (n : ℤ) :
    ∃ φ : homLoc ℳ s n →ₗ[R] 𝒩 n, Function.Bijective φ ∧
      ∀ (z : homLoc ℳ s n) (k : ℕ) (m : M), awayFrac M (xProd R s) k m = z →
        xProd R s ^ k • (φ z : N) = f m := by sorry
