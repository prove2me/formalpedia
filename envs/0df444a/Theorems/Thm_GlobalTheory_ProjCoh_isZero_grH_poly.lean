-- Prove2me | Theorems.Thm_GlobalTheory_ProjCoh_isZero_grH_poly
-- name    : GlobalTheory.ProjCoh.isZero_grH_poly
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:16:04.065624+00:00
-- url     : https://prove2.me/theorems/44fa6af7-0d9a-5f6b-8e09-2b788e3a636d
-- title:
--   Proj Coh: is Zero gr H poly
-- statement:
--   The Proj Coh construction uses the is Zero gr H poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NonemptyBasisPolyGrading.lean#L188-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NonemptyBasisPolyGrading.lean#L188-L192

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
variable (R : Type) [CommRing R] (N : ℕ) (n : ℤ)

theorem GlobalTheory.ProjCoh.isZero_grH_poly {p : ℕ} (h0 : p ≠ 0) (hp : p ≠ N) :
    IsZero (grH (Fin (N + 1)) (polyGrading (Fin (N + 1)) R) n p) := by sorry
