-- Prove2me | Theorems.Thm_GlobalTheory_exists_extend_adicCompletion
-- name    : GlobalTheory.exists_extend_adicCompletion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:35:56.571008+00:00
-- url     : https://prove2.me/theorems/a9fbf93b-e5c0-4988-b956-1133549b48fc
-- title:
--   Global Theory: exists extend adic Completion
-- statement:
--   The Global Theory construction uses the exists extend adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L28-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L28-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {A R : Type*} [CommRing A] [CommRing R]

theorem GlobalTheory.exists_extend_adicCompletion (φ : A →+* R) (J : Ideal A) (I : Ideal R)
    [IsAdicComplete I R] {k : ℕ} (hk : J.map φ ^ k ≤ I) :
    ∃ ψ : AdicCompletion J A →+* R, ψ.comp (algebraMap A (AdicCompletion J A)) = φ ∧
      ∀ (n : ℕ) (x : AdicCompletion J A) (a : A),
        AdicCompletion.evalₐ J (k * n) x = Ideal.Quotient.mk _ a → ψ x - φ a ∈ I ^ n := by sorry
