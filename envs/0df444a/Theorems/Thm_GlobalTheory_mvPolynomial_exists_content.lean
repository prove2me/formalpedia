-- Prove2me | Theorems.Thm_GlobalTheory_mvPolynomial_exists_content
-- name    : GlobalTheory.mvPolynomial_exists_content
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:30.360751+00:00
-- url     : https://prove2.me/theorems/5c50f16b-9b02-4b62-b748-e76bda1f9aa0
-- title:
--   Global Theory: mv Polynomial exists content
-- statement:
--   The Global Theory construction uses the mv Polynomial exists content property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MvPolynomialMapMaximalIdealIsPrime.lean#L34-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MvPolynomialMapMaximalIdealIsPrime.lean#L34-L55

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

theorem GlobalTheory.mvPolynomial_exists_content (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] (g : ℕ)
    (F : MvPolynomial (Fin g) O) (hF : F ≠ 0) :
    ∃ (π : O) (F' : MvPolynomial (Fin g) O), F = MvPolynomial.C π * F' ∧
      F' ∉ (IsLocalRing.maximalIdeal O).map (MvPolynomial.C : O →+* MvPolynomial (Fin g) O) := by sorry
