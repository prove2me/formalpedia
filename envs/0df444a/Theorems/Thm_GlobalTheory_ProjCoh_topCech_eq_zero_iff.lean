-- Prove2me | Theorems.Thm_GlobalTheory_ProjCoh_topCech_eq_zero_iff
-- name    : GlobalTheory.ProjCoh.topCech_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:34:05.573802+00:00
-- url     : https://prove2.me/theorems/44b2cbef-54f1-4227-a5f2-92a1c9f4c279
-- title:
--   Proj Coh: top Cech eq zero iff
-- statement:
--   The Proj Coh construction uses the top Cech eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NonemptyBasisPolyGrading.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NonemptyBasisPolyGrading.lean#L39-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfMonomialBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMonomialBasisCechCubePolynomialGrading
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexPolyGradingFiniteExact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NonemptyBasisPolyGrading
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.ProjCoh
variable {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type} [CommRing R]

theorem GlobalTheory.ProjCoh.topCech_eq_zero_iff (A : Cube.{0} ι R) {N : ℕ} (hN : Fintype.card ι = N + 1 + 1)
    (x : A.obj Finset.univ) :
    topCech A hN x = 0 ↔ ∃ y, Cube.d A (N + 1) y = CubeTop.topTerm A hN x := by sorry
