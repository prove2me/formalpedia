-- Prove2me | Theorems.Thm_GlobalTheory_T_companionMatrixOfCoeffs_charpoly_coeff_eq
-- name    : GlobalTheory.T.companionMatrixOfCoeffs_charpoly_coeff_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:30:07.121437+00:00
-- url     : https://prove2.me/theorems/70153035-0d00-44db-9cd3-0df254c514e7
-- title:
--   T: companion Matrix Of Coeffs charpoly coeff eq
-- statement:
--   The T construction uses the companion Matrix Of Coeffs charpoly coeff eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsCharpolyCoeffEqStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsCharpolyCoeffEqStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsCharpolyCoeffEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsCharpolyCoeffEqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.companionMatrixOfCoeffs_charpoly_coeff_eq : ∀ (k : Type) [CommRing k] (r : ℕ) (p : Fin r → k) (i : Fin r), (companion p).charpoly.coeff (i : ℕ) = p i := by sorry
