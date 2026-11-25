-- Prove2me | Theorems.Thm_GlobalTheory_grCubeVal_add
-- name    : GlobalTheory.grCubeVal_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:35:37.826269+00:00
-- url     : https://prove2.me/theorems/a1c2cc43-0f82-4361-8653-834ff665721f
-- title:
--   Global Theory: gr Cube Val add
-- statement:
--   The Global Theory construction uses the gr Cube Val add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCoboundaryOfFractionCocycleHomogeneousIdea.lean#L95-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCoboundaryOfFractionCocycleHomogeneousIdea.lean#L95-L96

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

theorem GlobalTheory.grCubeVal_add {s : Finset ι} (a b : (grCube ι ℳ n).obj s) :
    grCubeVal (a + b) = grCubeVal a + grCubeVal b := by sorry
