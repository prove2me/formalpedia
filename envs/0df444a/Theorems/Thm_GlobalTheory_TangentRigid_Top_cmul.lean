-- Prove2me | Theorems.Thm_GlobalTheory_TangentRigid_Top_cmul
-- name    : GlobalTheory.TangentRigid.Top.cmul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:08:31.449408+00:00
-- url     : https://prove2.me/theorems/dc7a9416-8ff7-4779-8e06-0158072715ad
-- title:
--   Top: cmul
-- statement:
--   The Top construction uses the cmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FirstOrderRigid.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FirstOrderRigid.lean#L22-L23

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

theorem GlobalTheory.TangentRigid.Top.cmul (a : k) (hp : Top p d c) : Top (C a * p) d (a * c) := by sorry
