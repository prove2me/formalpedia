-- Prove2me | Theorems.Thm_GlobalTheory_finite_of_finite_quot_map_of_isPrecomplete
-- name    : GlobalTheory.finite_of_finite_quot_map_of_isPrecomplete
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:47:01.78681+00:00
-- url     : https://prove2.me/theorems/2dd24c01-e6a2-4cb1-8017-7e6aedc95c01
-- title:
--   Global Theory: finite of finite quot map of is Precomplete
-- statement:
--   The Global Theory construction uses the finite of finite quot map of is Precomplete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiniteOfFiniteQuotMapOfIsPrecomplete.lean#L40-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiniteOfFiniteQuotMapOfIsPrecomplete.lean#L40-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiniteOfFiniteQuotMapOfIsPrecomplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.finite_of_finite_quot_map_of_isPrecomplete :
    ∀ (O A : Type) [CommRing O] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A]
      (J : Ideal O) [IsPrecomplete J O], J.map (algebraMap O A) ≠ ⊤ →
      Module.Finite O (A ⧸ J.map (algebraMap O A)) → Module.Finite O A := by sorry
