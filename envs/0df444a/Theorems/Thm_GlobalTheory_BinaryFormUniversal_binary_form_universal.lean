-- Prove2me | Theorems.Thm_GlobalTheory_BinaryFormUniversal_binary_form_universal
-- name    : GlobalTheory.BinaryFormUniversal.binary_form_universal
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:01:05.746775+00:00
-- url     : https://prove2.me/theorems/2144a9a4-8fae-427a-b5b6-3b3614ea25fd
-- title:
--   Binary Form Universal: binary form universal
-- statement:
--   The Binary Form Universal construction uses the binary form universal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/BinaryFormUniversal.lean#L9-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/BinaryFormUniversal.lean#L9-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_BinaryFormUniversal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.BinaryFormUniversal
open Polynomial

theorem GlobalTheory.BinaryFormUniversal.binary_form_universal {k : Type u_1} [Field k] [Finite k] {a n : k}
    (hD : a ^ (2 : ℕ) - (4 : k) * n ≠ (0 : k)) (u : k) :
    ∃ (r : k) (s : k), r ^ (2 : ℕ) + a * r * s + n * s ^ (2 : ℕ) = u := by sorry
