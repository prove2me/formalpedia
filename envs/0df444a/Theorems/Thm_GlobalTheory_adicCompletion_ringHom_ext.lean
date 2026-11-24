-- Prove2me | Theorems.Thm_GlobalTheory_adicCompletion_ringHom_ext
-- name    : GlobalTheory.adicCompletion_ringHom_ext
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:10:47.073231+00:00
-- url     : https://prove2.me/theorems/e199990c-f18f-422e-9f33-c80833265385
-- title:
--   Global Theory: adic Completion ring Hom ext
-- statement:
--   The Global Theory construction uses the adic Completion ring Hom ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L61-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L61-L85

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

theorem GlobalTheory.adicCompletion_ringHom_ext {J : Ideal A} (hJ : J.FG) (I : Ideal R) [IsHausdorff I R]
    {ψ ψ' : AdicCompletion J A →+* R} {k : ℕ}
    (hk : J.map (ψ.comp (algebraMap A (AdicCompletion J A))) ^ k ≤ I)
    (h : ψ.comp (algebraMap A (AdicCompletion J A)) =
      ψ'.comp (algebraMap A (AdicCompletion J A))) : ψ = ψ' := by sorry
