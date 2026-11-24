-- Prove2me | Theorems.Thm_GlobalTheory_DI_pow_smul_mem_forms_powMul
-- name    : GlobalTheory.DI.pow_smul_mem_forms_powMul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:36:07.244894+00:00
-- url     : https://prove2.me/theorems/d77a562b-871f-47fd-b702-b934ab44a8f6
-- title:
--   DI: pow smul mem forms pow Mul
-- statement:
--   The DI construction uses the pow smul mem forms pow Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/SplittingIntegralFormsBound.lean#L8-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/SplittingIntegralFormsBound.lean#L8-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AlternatingProductIntegral
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_SplittingIntegralFormsBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI

theorem GlobalTheory.DI.pow_smul_mem_forms_powMul {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    (p : ℕ) (A B : Set K) (L : Set V) (q : ℕ) (b : K) (hb : b ∈ B) (y : ExteriorAlgebra K V)
    (hy : y ∈ forms A L q) : b ^ p • y ∈ forms {z | ∃ c ∈ B, ∃ a ∈ A, z = c ^ p * a} L q := by sorry
