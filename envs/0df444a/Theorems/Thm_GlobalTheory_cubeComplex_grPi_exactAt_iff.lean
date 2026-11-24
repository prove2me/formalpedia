-- Prove2me | Theorems.Thm_GlobalTheory_cubeComplex_grPi_exactAt_iff
-- name    : GlobalTheory.cubeComplex_grPi_exactAt_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:13.767639+00:00
-- url     : https://prove2.me/theorems/b9d20c97-8360-45a1-a116-3845a283f24a
-- title:
--   Global Theory: cube Complex gr Pi exact At iff
-- statement:
--   The Global Theory construction uses the cube Complex gr Pi exact At iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsAwayFracOfMemHomLoc.lean#L826-L831
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsAwayFracOfMemHomLoc.lean#L826-L831

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open DirectSum MvPolynomial CategoryTheory
universe u
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type} {R : Type u} [CommRing R] {κ : Type} [Fintype κ]
  {M : κ → Type u} [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)]
  [∀ k, Module (MvPolynomial ι R) (M k)] [∀ k, IsScalarTower R (MvPolynomial ι R) (M k)]
  (ℳ : ∀ k, ℤ → Submodule R (M k)) [∀ k, PolyGradedSMul ι (ℳ k)]
variable [LinearOrder ι]
variable [Finite ι]

theorem GlobalTheory.cubeComplex_grPi_exactAt_iff (n : ℤ) (p : ℕ) :
    (cubeComplex (grCube ι (grPi ℳ) n)).ExactAt p ↔
      ∀ k, (cubeComplex (grCube ι (ℳ k) n)).ExactAt p := by sorry
