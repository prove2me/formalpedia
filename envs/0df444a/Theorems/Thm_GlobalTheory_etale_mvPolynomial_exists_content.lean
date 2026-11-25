-- Prove2me | Theorems.Thm_GlobalTheory_etale_mvPolynomial_exists_content
-- name    : GlobalTheory.etale_mvPolynomial_exists_content
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:18:34.127526+00:00
-- url     : https://prove2.me/theorems/b679a89e-83f4-4ca8-9670-9241c493656c
-- title:
--   Global Theory: etale mv Polynomial exists content
-- statement:
--   The Global Theory construction uses the etale mv Polynomial exists content property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ValuationRingExistsAssociatedOfSumEqZero.lean#L148-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ValuationRingExistsAssociatedOfSumEqZero.lean#L148-L247

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPolynomialMapMaximalIdealIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingOfFlatOfFormallyUnramified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero
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

theorem GlobalTheory.etale_mvPolynomial_exists_content :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (g : ℕ) (B : Type) [CommRing B] [IsDomain B] [Algebra O B] [Algebra (MvPolynomial (Fin g) O) B] [IsScalarTower O (MvPolynomial (Fin g) O) B] [Algebra.Etale (MvPolynomial (Fin g) O) B], ((IsLocalRing.maximalIdeal O).map (algebraMap O B)).IsPrime → ∀ b : B, b ≠ 0 → ∃ (π : O) (b' : B), b = algebraMap O B π * b' ∧ b' ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O B) := by sorry
