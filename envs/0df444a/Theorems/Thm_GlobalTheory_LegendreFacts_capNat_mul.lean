-- Prove2me | Theorems.Thm_GlobalTheory_LegendreFacts_capNat_mul
-- name    : GlobalTheory.LegendreFacts.capNat_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:58.522692+00:00
-- url     : https://prove2.me/theorems/c7f67145-7e52-4b80-a0b4-ec12c7c606bd
-- title:
--   Legendre Facts: cap Nat mul
-- statement:
--   The Legendre Facts construction uses the cap Nat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LegendreAndCapelli.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LegendreAndCapelli.lean#L21-L28

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
open GlobalTheory GlobalTheory.LegendreFacts
open GlobalTheory.LegendreBounds

theorem GlobalTheory.LegendreFacts.capNat_mul (n0 x : ℕ) :
    capNat n0 x * ∏ c ∈ Finset.range n0, c.factorial
      = ∏ c ∈ Finset.range n0, (x + c).factorial := by sorry
