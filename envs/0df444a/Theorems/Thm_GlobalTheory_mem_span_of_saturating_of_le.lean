-- Prove2me | Theorems.Thm_GlobalTheory_mem_span_of_saturating_of_le
-- name    : GlobalTheory.mem_span_of_saturating_of_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:49:21.048726+00:00
-- url     : https://prove2.me/theorems/51ed5959-2981-4eb8-967f-32a5628bec61
-- title:
--   Global Theory: mem span of saturating of le
-- statement:
--   The Global Theory construction uses the mem span of saturating of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemSpanOfSaturatingOfLe.lean#L9-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/MemSpanOfSaturatingOfLe.lean#L9-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexGradedModuleExactAtOfLargeDegreeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemSpanOfSaturatingOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory

theorem GlobalTheory.mem_span_of_saturating_of_le : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (r : ℕ) (d : Fin r → ℤ) (g : Fin r → M), (∀ l, g l ∈ ℳ (d l)) → (∀ (i : ι) (y : M), ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (Set.range g)) → (∀ y : M, (∀ i : ι, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y = 0) → y = 0) → ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ y ∈ ℳ n, y ∈ Submodule.span (MvPolynomial ι R) (Set.range g) := by sorry
