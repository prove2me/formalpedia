-- Prove2me | Theorems.Thm_GlobalTheory_exists_xProd_pow_smul_monomial
-- name    : GlobalTheory.exists_xProd_pow_smul_monomial
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:45.437844+00:00
-- url     : https://prove2.me/theorems/e96fbe6c-96f1-4dbb-84f4-9d5e5ddc04b1
-- title:
--   Global Theory: exists x Prod pow smul monomial
-- statement:
--   The Global Theory construction uses the exists x Prod pow smul monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMonomialBasisCechCubePolynomialGrading.lean#L10-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMonomialBasisCechCubePolynomialGrading.lean#L10-L18

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

theorem GlobalTheory.exists_xProd_pow_smul_monomial {ι : Type} [DecidableEq ι] (R : Type) [CommRing R]
    (s : Finset ι) (j : ℕ) (m : ι →₀ ℕ) :
    ∃ m' : ι →₀ ℕ, (∀ i, m' i = m i + if i ∈ s then j else 0) ∧
      xProd R s ^ j • (monomial m 1 : MvPolynomial ι R) = monomial m' 1 := by sorry
