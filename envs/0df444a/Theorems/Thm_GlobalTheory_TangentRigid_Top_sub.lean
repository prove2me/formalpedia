-- Prove2me | Theorems.Thm_GlobalTheory_TangentRigid_Top_sub
-- name    : GlobalTheory.TangentRigid.Top.sub
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:08:24.895466+00:00
-- url     : https://prove2.me/theorems/5f29d48a-4c4c-4d37-9032-fd7b7eb767de
-- title:
--   Top: sub
-- statement:
--   The Top construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FirstOrderRigid.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FirstOrderRigid.lean#L19-L20

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

theorem GlobalTheory.TangentRigid.Top.sub (hp : Top p d c) (hq : Top q d c') : Top (p - q) d (c - c') := by sorry
