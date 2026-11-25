-- Prove2me | Theorems.Thm_GlobalTheory_TeichPair_ge_pow_sub
-- name    : GlobalTheory.TeichPair.ge_pow_sub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:14:37.165735+00:00
-- url     : https://prove2.me/theorems/afa6c803-48e5-456a-94a5-8b8cfe1c9cc8
-- title:
--   Teich Pair: ge pow sub
-- statement:
--   The Teich Pair construction uses the ge pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EqZeroOfGe.lean#L118-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EqZeroOfGe.lean#L118-L125

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqZeroOfGe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.TeichPair
variable {C : Type} [Field C]

theorem GlobalTheory.TeichPair.ge_pow_sub {V : VF C} {w : ℝ} {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) (h : V.Ge w (a - b)) (m : ℕ) :
    V.Ge w (a ^ m - b ^ m) := by sorry
