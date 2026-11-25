-- Prove2me | Theorems.Thm_GlobalTheory_cubeComplex_polyGrading_finite_exact
-- name    : GlobalTheory.cubeComplex_polyGrading_finite_exact
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:39.74562+00:00
-- url     : https://prove2.me/theorems/c21794bd-6229-4bfc-8829-a8ddd0f4e89d
-- title:
--   Global Theory: cube Complex poly Grading finite exact
-- statement:
--   The Global Theory construction uses the cube Complex poly Grading finite exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexPolyGradingFiniteExact.lean#L25-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexPolyGradingFiniteExact.lean#L25-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfMonomialBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGradingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexPolyGradingFiniteExact
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

theorem GlobalTheory.cubeComplex_polyGrading_finite_exact : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (n : ℤ), (∀ p, Module.Finite R ((cubeComplex (grCube ι (polyGrading ι R) n)).homology p)) ∧ (1 ≤ n → ∀ p, (cubeComplex (grCube ι (polyGrading ι R) n)).ExactAt p) := by sorry
