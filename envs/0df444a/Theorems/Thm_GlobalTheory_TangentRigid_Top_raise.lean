-- Prove2me | Theorems.Thm_GlobalTheory_TangentRigid_Top_raise
-- name    : GlobalTheory.TangentRigid.Top.raise
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:08:34.68346+00:00
-- url     : https://prove2.me/theorems/4f8eb2f3-8860-4680-91a3-5c6d887f35e4
-- title:
--   Top: raise
-- statement:
--   The Top construction uses the raise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FirstOrderRigid.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FirstOrderRigid.lean#L25-L26

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

theorem GlobalTheory.TangentRigid.Top.raise (hp : Top p d c) (h : d < e) : Top p e 0 := by sorry
