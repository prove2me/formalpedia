-- Prove2me | Theorems.Thm_GlobalTheory_coeff_aeval_C_mul_X
-- name    : GlobalTheory.coeff_aeval_C_mul_X
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:09:19.936669+00:00
-- url     : https://prove2.me/theorems/6e5d2616-a608-4488-a913-0e8a7d2f3536
-- title:
--   Global Theory: coeff aeval C mul X
-- statement:
--   The Global Theory construction uses the coeff aeval C mul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsCompleteDiscreteValuationRingOfMemClosureC.lean#L9-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsCompleteDiscreteValuationRingOfMemClosureC.lean#L9-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDiscreteValuationRingOfMemClosureC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.coeff_aeval_C_mul_X {K A J : Type*} [CommRing K] [CommRing A] [Algebra K A] (w : J → A)
    (G : MvPolynomial J K) (d : ℕ) :
    (MvPolynomial.aeval (fun j => Polynomial.C (w j) * Polynomial.X) G).coeff d =
      MvPolynomial.aeval w (MvPolynomial.homogeneousComponent d G) := by sorry
