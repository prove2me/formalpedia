-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_monomial_basis_cechCube_polynomialGrading
-- name    : GlobalTheory.T.exists_monomial_basis_cechCube_polynomialGrading
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:01:06.963626+00:00
-- url     : https://prove2.me/theorems/b2570b42-8f64-4a61-948e-f02df8caabf6
-- title:
--   T: exists monomial basis cech Cube polynomial Grading
-- statement:
--   The T construction uses the exists monomial basis cech Cube polynomial Grading property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMonomialBasisCechCubePolynomialGradingStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMonomialBasisCechCubePolynomialGradingStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGrading
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGradingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

theorem GlobalTheory.T.exists_monomial_basis_cechCube_polynomialGrading : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (n : ℤ), ∃ b : ∀ s : Finset ι, Module.Basis {a : {a : ι → ℤ // ∑ i, a i = n} // Finset.univ.filter (fun i => a.1 i < 0) ⊆ s} R ((grCube ι (polyGrading ι R) n).obj s), ∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : {a : ι → ℤ // ∑ i, a i = n} // Finset.univ.filter (fun i => a.1 i < 0) ⊆ s}), Cube.res (grCube ι (polyGrading ι R) n) h (b s a) = b t ⟨a.1, a.2.trans h⟩ := by sorry
