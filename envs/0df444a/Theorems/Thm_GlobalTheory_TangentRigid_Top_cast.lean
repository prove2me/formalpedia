-- Prove2me | Theorems.Thm_GlobalTheory_TangentRigid_Top_cast
-- name    : GlobalTheory.TangentRigid.Top.cast
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:08:38.018602+00:00
-- url     : https://prove2.me/theorems/a8d0de09-210d-4660-8086-c7c66eef9527
-- title:
--   Top: cast
-- statement:
--   The Top construction uses the cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FirstOrderRigid.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FirstOrderRigid.lean#L28-L30

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

theorem GlobalTheory.TangentRigid.Top.cast {p' : k[X]} (hp : Top p d c) (h0 : p = p') (h : d = e) (h' : c = c') :
    Top p' e c' := by sorry
