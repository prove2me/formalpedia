-- Prove2me | Theorems.Thm_GlobalTheory_awayFrac_monomial_congr
-- name    : GlobalTheory.awayFrac_monomial_congr
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:53.461152+00:00
-- url     : https://prove2.me/theorems/e7576807-9a04-4d57-9794-ac184d21bbc0
-- title:
--   Global Theory: away Frac monomial congr
-- statement:
--   The Global Theory construction uses the away Frac monomial congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMonomialBasisCechCubePolynomialGrading.lean#L20-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMonomialBasisCechCubePolynomialGrading.lean#L20-L36

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

theorem GlobalTheory.awayFrac_monomial_congr {ι : Type} [DecidableEq ι] (R : Type) [CommRing R]
    (s : Finset ι) (a : ι → ℤ) {k j : ℕ} {m m' : ι →₀ ℕ}
    (hm : ∀ i, (m i : ℤ) = a i + if i ∈ s then (k : ℤ) else 0)
    (hm' : ∀ i, (m' i : ℤ) = a i + if i ∈ s then (j : ℤ) else 0) :
    awayFrac (MvPolynomial ι R) (xProd R s) k (monomial m 1) =
      awayFrac (MvPolynomial ι R) (xProd R s) j (monomial m' 1) := by sorry
