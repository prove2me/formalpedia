-- Prove2me | Theorems.Thm_GlobalTheory_grCubeVal_res
-- name    : GlobalTheory.grCubeVal_res
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:34:40.967379+00:00
-- url     : https://prove2.me/theorems/9d6d4d67-6f0c-4e1a-82bc-33c04f46ee2b
-- title:
--   Global Theory: gr Cube Val res
-- statement:
--   The Global Theory construction uses the gr Cube Val res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCoboundaryOfFractionCocycleHomogeneousIdea.lean#L106-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCoboundaryOfFractionCocycleHomogeneousIdea.lean#L106-L107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexGradedModuleExactAtOfLargeDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoboundaryOfFractionCocycleHomogeneousIdea
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial DirectSum
open GlobalTheory
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ] {n : ℤ}

theorem GlobalTheory.grCubeVal_res {s t : Finset ι} (h : s ⊆ t) (z : (grCube ι ℳ n).obj s) :
    grCubeVal (Cube.res (grCube ι ℳ n) h z) = locRes X M h (grCubeVal z) := by sorry
