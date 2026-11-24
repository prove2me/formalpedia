-- Prove2me | Theorems.Thm_GlobalTheory_JR_CompanionCharpoly_charpoly_companion_coeff_ring
-- name    : GlobalTheory.JR.CompanionCharpoly.charpoly_companion_coeff_ring
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:23:34.07127+00:00
-- url     : https://prove2.me/theorems/fc9aa09f-b78b-4b84-9eac-2f6669d73801
-- title:
--   Companion Charpoly: charpoly companion coeff ring
-- statement:
--   The Companion Charpoly construction uses the charpoly companion coeff ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsCharpolyCoeffEq.lean#L26-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsCharpolyCoeffEq.lean#L26-L36

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

theorem GlobalTheory.JR.CompanionCharpoly.charpoly_companion_coeff_ring :
    ∀ (k : Type) [CommRing k] (r : ℕ) (p : Fin r → k) (i : Fin r), (companion p).charpoly.coeff (i : ℕ) = p i := by sorry
