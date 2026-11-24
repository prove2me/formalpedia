-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_extend_adicCompletion
-- name    : GlobalTheory.existsUnique_extend_adicCompletion
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:29:19.974082+00:00
-- url     : https://prove2.me/theorems/cd3709a9-46a6-462e-afde-fbfce26f9463
-- title:
--   Global Theory: exists Unique extend adic Completion
-- statement:
--   The Global Theory construction uses the exists Unique extend adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L87-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L87-L93

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

theorem GlobalTheory.existsUnique_extend_adicCompletion (φ : A →+* R) {J : Ideal A} (hJ : J.FG) (I : Ideal R)
    [IsAdicComplete I R] (hk : ∃ k : ℕ, J.map φ ^ k ≤ I) :
    ∃! ψ : AdicCompletion J A →+* R, ψ.comp (algebraMap A (AdicCompletion J A)) = φ := by sorry
