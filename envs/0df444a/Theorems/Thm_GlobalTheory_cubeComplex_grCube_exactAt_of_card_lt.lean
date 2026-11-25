-- Prove2me | Theorems.Thm_GlobalTheory_cubeComplex_grCube_exactAt_of_card_lt
-- name    : GlobalTheory.cubeComplex_grCube_exactAt_of_card_lt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:27:36.245798+00:00
-- url     : https://prove2.me/theorems/6b96ed1c-f5b7-4bb1-a5bc-65d79c018293
-- title:
--   Global Theory: cube Complex gr Cube exact At of card lt
-- statement:
--   The Global Theory construction uses the cube Complex gr Cube exact At of card lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexGradedModuleExactAtOfLargeDegree.lean#L15-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexGradedModuleExactAtOfLargeDegree.lean#L15-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexGrFreeFiniteAndExactAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexGradedModuleExactAtOfLargeDegree
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

theorem GlobalTheory.cubeComplex_grCube_exactAt_of_card_lt (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] [IsNoetherianRing R] (q : ℕ) :
    ∀ (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
      [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
      [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M →
      ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ p, Fintype.card ι < p + q →
        (cubeComplex (grCube ι ℳ n)).ExactAt p := by sorry
