-- Prove2me | Theorems.Thm_GlobalTheory_CharacterConductorBall_exists_conductor
-- name    : GlobalTheory.CharacterConductorBall.exists_conductor
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:10:10.169144+00:00
-- url     : https://prove2.me/theorems/990f1600-2778-4265-9bb5-591899bc20d8
-- title:
--   Character Conductor Ball: exists conductor
-- statement:
--   The Character Conductor Ball construction uses the exists conductor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/EqOneOfNormSubOneLt.lean#L84-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/EqOneOfNormSubOneLt.lean#L84-L125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfNormSubOneLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CharacterConductorBall

theorem GlobalTheory.CharacterConductorBall.exists_conductor {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hc : Continuous (ψ : K → ℂ)) (hψ : ∃ t : K, ψ t ≠ 1) :
    ∃ n : ℤ, ∀ t : K,
      (∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) ↔
        Valued.v t ≤ WithZero.exp n := by sorry
