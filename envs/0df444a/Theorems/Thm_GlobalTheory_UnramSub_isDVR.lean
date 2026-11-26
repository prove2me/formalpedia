-- Prove2me | Theorems.Thm_GlobalTheory_UnramSub_isDVR
-- name    : GlobalTheory.UnramSub.isDVR
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:42:30.103583+00:00
-- url     : https://prove2.me/theorems/535877ec-cd09-5bbf-bd27-8cd30dfb74e0
-- title:
--   Unram Sub: is DVR
-- statement:
--   The Unram Sub construction uses the is DVR property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnramSub.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnramSub.lean#L16-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnramSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.UnramSub
variable {V F : Type} [CommRing V] [Field F] {i : V →+* F}

theorem GlobalTheory.UnramSub.isDVR {T : Subring F} (h : UnramSub i T) : IsDiscreteValuationRing T := by sorry
