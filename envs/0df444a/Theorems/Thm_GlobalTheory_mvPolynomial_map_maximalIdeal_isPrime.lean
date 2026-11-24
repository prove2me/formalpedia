-- Prove2me | Theorems.Thm_GlobalTheory_mvPolynomial_map_maximalIdeal_isPrime
-- name    : GlobalTheory.mvPolynomial_map_maximalIdeal_isPrime
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:12:13.028799+00:00
-- url     : https://prove2.me/theorems/1bbdcb9b-671c-4917-ba52-fb55f51b95e2
-- title:
--   Global Theory: mv Polynomial map maximal Ideal is Prime
-- statement:
--   The Global Theory construction uses the mv Polynomial map maximal Ideal is Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MvPolynomialMapMaximalIdealIsPrime.lean#L24-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MvPolynomialMapMaximalIdealIsPrime.lean#L24-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPolynomialMapMaximalIdealIsPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.mvPolynomial_map_maximalIdeal_isPrime (O : Type) [CommRing O] [IsLocalRing O] (g : ℕ) :
    ((IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O)).IsPrime := by sorry
