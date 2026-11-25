-- Prove2me | Theorems.Thm_GlobalTheory_exists_laurent_numerator
-- name    : GlobalTheory.exists_laurent_numerator
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:54:58.986435+00:00
-- url     : https://prove2.me/theorems/ee066cf2-4bbb-4e08-9632-249da97b5a5e
-- title:
--   Global Theory: exists laurent numerator
-- statement:
--   The Global Theory construction uses the exists laurent numerator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMonomialBasisCechCubePolynomialGrading.lean#L38-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMonomialBasisCechCubePolynomialGrading.lean#L38-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LinearIndependentLaurentMonomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanLaurentMonomialEqHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGrading
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

theorem GlobalTheory.exists_laurent_numerator {ι : Type} [DecidableEq ι] [Fintype ι] (s : Finset ι)
    (a : ι → ℤ) (ha : ∀ i, i ∉ s → 0 ≤ a i) :
    ∃ (k : ℕ) (m : ι →₀ ℕ), ∀ i, (m i : ℤ) = a i + if i ∈ s then (k : ℤ) else 0 := by sorry
