-- Prove2me | Theorems.Thm_OnlineCRS_Combine_chi_first_antitone
-- name    : OnlineCRS.Combine.chi_first_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:20:13.471926+00:00
-- url     : https://prove2.me/theorems/9c92b34d-d87b-440e-9000-06c1664e3efb
-- title:
--   Proof of Lemma 2.11, p. 16 — χₑ decreases in its first argument
-- statement:
--   Fix an element $e$ and families $F,F'$ of subsets of the ground set. For active sets $A\subseteq B$,
--
--   $$
--   \chi_e(B,F,F')\Longrightarrow\chi_e(A,F,F').
--   $$
--
--   Shrinking the active set leaves fewer candidate subsets to check. This is the second monotonicity claim in the proof of Lemma 2.11.
-- source:
--   arXiv:1508.00142v2, §2.4, proof of Lemma 2.11, p. 16, third sentence

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Combination

namespace OnlineCRS.Combine

/-- The first-argument monotonicity of χₑ used in Lemma 2.11, p. 16. -/
theorem chi_first_antitone {α : Type} [DecidableEq α]
    (e : α) (A B : Finset α) (F F' : Finset (Finset α))
    (h : A ⊆ B) : chi e B F F' → chi e A F F' := by sorry

end OnlineCRS.Combine
