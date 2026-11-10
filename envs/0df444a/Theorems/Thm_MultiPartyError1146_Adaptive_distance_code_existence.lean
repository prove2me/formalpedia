-- Prove2me | Theorems.Thm_MultiPartyError1146_Adaptive_distance_code_existence
-- name    : MultiPartyError1146.Adaptive.distance_code_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T18:33:29.797204+00:00
-- url     : https://prove2.me/theorems/d35fd86c-f897-4fa1-96ac-87494c5c830a
-- title:
--   Lemma 3.2 — constant-rate binary codes
-- statement:
--   For every $\epsilon>0$ there is a uniform constant $a\ge1$ such that every positive input length $m$ admits an injective binary encoder of positive length $\ell\le am$ with
--   $$d_H(C(x),C(y))\ge(1/2-\epsilon)\ell\quad(x\ne y).$$
--   The uniform length bound states constant rate even when $\epsilon\ge1/2$, where the displayed distance bound alone is vacuous. The result supplies the outer and packet codes.
--
--   Differences from the source:
--   - encoding: constant-rate code of input length n → one coefficient a depending only on ε, with injectivity and positive length explicit; reason: these are the ordinary code and rate conventions
--   - encoding: one-based party, time and message-coordinate labels → Fin indices, Boolean bits and optional-Boolean received symbols with zero-based iteration indices; reason: fixed finite relabelings preserve every input, action and error; supporting local quantities are execution-derived
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Lemma 3.2, printed p.18, PDF p.20

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Codes

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

theorem distance_code_existence :
    ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 1 ≤ a ∧ ∀ m : ℕ, 1 ≤ m →
      ∃ C : BinaryCode (Fin m → Bool), 1 ≤ C.length ∧
        (C.length : ℝ) ≤ a * m ∧ Function.Injective C.encode ∧
        C.HasDistance ((1 : ℝ) / 2 - ε) := by sorry

end MultiPartyError1146.Adaptive
