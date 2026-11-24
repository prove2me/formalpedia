-- Prove2me | Theorems.Thm_GlobalTheory_JR_CompanionCharpoly_coeff_universal
-- name    : GlobalTheory.JR.CompanionCharpoly.coeff_universal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:23:41.019379+00:00
-- url     : https://prove2.me/theorems/9c491044-b516-4b0f-864d-dc55c66827d4
-- title:
--   Companion Charpoly: coeff universal
-- statement:
--   The Companion Charpoly construction uses the coeff universal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsCharpolyCoeffEq.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsCharpolyCoeffEq.lean#L14-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsCharpolyCoeffEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.CompanionCharpoly

theorem GlobalTheory.JR.CompanionCharpoly.coeff_universal (r : ℕ) (i : Fin r) :
    (companion (fun j : Fin r => (MvPolynomial.X j : MvPolynomial (Fin r) ℤ))).charpoly.coeff (i : ℕ) =
      MvPolynomial.X i := by sorry
