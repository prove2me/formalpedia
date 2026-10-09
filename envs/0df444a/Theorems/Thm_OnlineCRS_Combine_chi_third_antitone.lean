-- Prove2me | Theorems.Thm_OnlineCRS_Combine_chi_third_antitone
-- name    : OnlineCRS.Combine.chi_third_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:20:19.245059+00:00
-- url     : https://prove2.me/theorems/26e131cc-1ea1-445b-9f13-19fbc47757e2
-- title:
--   Proof of Lemma 2.11, p. 16 — χₑ decreases in its third argument
-- statement:
--   Fix an element $e$, an active set $A$, and families $F,F',F''$ of subsets of the ground set. If $F''\subseteq F'$, then
--
--   $$
--   \chi_e(A,F,F')\Longrightarrow\chi_e(A,F,F'').
--   $$
--
--   Restricting the family of candidate previously selected sets preserves the selectability event. This is the first monotonicity claim used in Lemma 2.11.
-- source:
--   arXiv:1508.00142v2, §2.4, proof of Lemma 2.11, p. 16, first sentence

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Combination

namespace OnlineCRS.Combine

/-- The third-argument monotonicity of χₑ used in Lemma 2.11, p. 16. -/
theorem chi_third_antitone {α : Type} [DecidableEq α]
    (e : α) (A : Finset α) (F F' F'' : Finset (Finset α))
    (h : F'' ⊆ F') : chi e A F F' → chi e A F F'' := by sorry

end OnlineCRS.Combine
