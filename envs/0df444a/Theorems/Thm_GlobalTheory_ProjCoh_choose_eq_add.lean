-- Prove2me | Theorems.Thm_GlobalTheory_ProjCoh_choose_eq_add
-- name    : GlobalTheory.ProjCoh.choose_eq_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:15:57.696258+00:00
-- url     : https://prove2.me/theorems/cdd87e81-74b4-58e5-97d1-72664f96f4f1
-- title:
--   Proj Coh: choose eq add
-- statement:
--   The Proj Coh construction uses the choose eq add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NonemptyBasisPolyGrading.lean#L143-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NonemptyBasisPolyGrading.lean#L143-L153

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

theorem GlobalTheory.ProjCoh.choose_eq_add (N : ℕ) (hN : 1 ≤ N) (n : ℤ) :
    Ring.choose (n + N) N = ((n + N).toNat.choose N : ℤ) + (-1) ^ N * (-n - 1).toNat.choose N := by sorry
