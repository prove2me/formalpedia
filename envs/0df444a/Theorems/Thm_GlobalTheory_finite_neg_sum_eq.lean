-- Prove2me | Theorems.Thm_GlobalTheory_finite_neg_sum_eq
-- name    : GlobalTheory.finite_neg_sum_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:06.651047+00:00
-- url     : https://prove2.me/theorems/a5fff12f-9254-4728-9b7e-52277e642cbb
-- title:
--   Global Theory: finite neg sum eq
-- statement:
--   The Global Theory construction uses the finite neg sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexPolyGradingFiniteExact.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexPolyGradingFiniteExact.lean#L11-L23

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

theorem GlobalTheory.finite_neg_sum_eq (ι : Type) [Fintype ι] (n : ℤ) :
    {a : {a : ι → ℤ // ∑ i, a i = n} |
      Finset.univ.filter (fun i => a.1 i < 0) = Finset.univ}.Finite := by sorry
