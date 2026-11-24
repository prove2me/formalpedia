-- Prove2me | Theorems.Thm_GlobalTheory_isAlgebraic_of_subring_isAlgebraic
-- name    : GlobalTheory.isAlgebraic_of_subring_isAlgebraic
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:56:00.161875+00:00
-- url     : https://prove2.me/theorems/903fdfb9-6442-4c18-917f-708cff0d12a9
-- title:
--   Global Theory: is Algebraic of subring is Algebraic
-- statement:
--   The Global Theory construction uses the is Algebraic of subring is Algebraic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAlgebraicOfSubringIsAlgebraic.lean#L7-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAlgebraicOfSubringIsAlgebraic.lean#L7-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAlgebraicOfSubringIsAlgebraic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Algebra

theorem GlobalTheory.isAlgebraic_of_subring_isAlgebraic {L : Type} [Field L] [Algebra ℂ L]
    (S : Subalgebra ℂ L) (B : Subring L) (z : L)
    (hB : ∀ b ∈ B, IsAlgebraic S b) (hz : IsAlgebraic B z) : IsAlgebraic S z := by sorry
