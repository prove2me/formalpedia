-- Prove2me | Theorems.Thm_GlobalTheory_TangentRigid_Top_xder
-- name    : GlobalTheory.TangentRigid.Top.xder
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:08:46.859718+00:00
-- url     : https://prove2.me/theorems/bf6946d5-d5bf-4d3b-a566-c9064ddf0428
-- title:
--   Top: xder
-- statement:
--   The Top construction uses the xder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FirstOrderRigid.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FirstOrderRigid.lean#L42-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FirstOrderRigid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TangentRigid
variable {k : Type} [Field k] {p q : k[X]} {d e : ℕ} {c c' : k}

theorem GlobalTheory.TangentRigid.Top.xder (hp : Top p d c) : Top (X * derivative p) d (d * c) := by sorry
