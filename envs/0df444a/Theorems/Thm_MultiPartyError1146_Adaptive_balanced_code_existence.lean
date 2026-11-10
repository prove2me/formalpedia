-- Prove2me | Theorems.Thm_MultiPartyError1146_Adaptive_balanced_code_existence
-- name    : MultiPartyError1146.Adaptive.balanced_code_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T18:33:26.678516+00:00
-- url     : https://prove2.me/theorems/081359aa-66de-4fcc-b4cd-05c4034ddc69
-- title:
--   Lemma 3.4 — constant-rate balanced binary codes
-- statement:
--   For every $\epsilon>0$ there is a uniform $a\ge1$ such that each positive $m$ has an injective binary code of positive length $\ell\le am$ satisfying, for all three distinct messages and all prescribed three-bit patterns,
--   $$|\{t:(C_t(x_1),C_t(x_2),C_t(x_3))=(b_1,b_2,b_3)\}|\ge(1-\epsilon)\ell/8.$$
--   This is joint-pattern balance, used for collision-free speaking slots in phase 3. For one-bit messages, the three-distinct-message condition is vacuous; the later padded ternary-view domain has at least three messages.
--
--   Differences from the source:
--   - encoding: constant-rate (3,1−ε)-balanced code → uniform length coefficient, injective encoder and joint-pattern predicate; reason: the code convention and all pattern quantifiers are explicit
--   - encoding: one-based party, time and message-coordinate labels → Fin indices, Boolean bits and optional-Boolean received symbols with zero-based iteration indices; reason: fixed finite relabelings preserve every input, action and error; supporting local quantities are execution-derived
--   - encoding: ε>0 in Lemma 3.4 and positive ζ in Definition 3.3 → the defining balance inequality is total for every real ζ, including ζ=1−ε≤0; reason: for ε≥1 only the balance inequality is vacuous; injective positive-length constant-rate encoding is still required
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Lemma 3.4, printed p.18, PDF p.20

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Codes

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

theorem balanced_code_existence :
    ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 1 ≤ a ∧ ∀ m : ℕ, 1 ≤ m →
      ∃ C : BinaryCode (Fin m → Bool), 1 ≤ C.length ∧
        (C.length : ℝ) ≤ a * m ∧ Function.Injective C.encode ∧ C.Balanced 3 (1 - ε) := by sorry

end MultiPartyError1146.Adaptive
