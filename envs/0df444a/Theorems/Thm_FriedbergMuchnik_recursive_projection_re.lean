-- Prove2me | Theorems.Thm_FriedbergMuchnik_recursive_projection_re
-- name    : FriedbergMuchnik.recursive_projection_re
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T20:04:00.400579+00:00
-- url     : https://prove2.me/theorems/a032b4e0-aa71-45ef-87fa-ae94f6f4ad0e
-- title:
--   Existential projection of a computable relation is c.e.
-- statement:
--   Let $R\subseteq\mathbb N\times\mathbb N$ be a computable relation: membership of $(n,s)$ is decidable by a total computable procedure. Its projection onto the first coordinate is computably enumerable:
--
--   $$\operatorname{Computable}(R)\quad\Longrightarrow\quad\operatorname{RE}\bigl(\{n\in\mathbb N:\exists s\in\mathbb N,\ R(n,s)\}\bigr).$$
--
--   No bound on the witness $s$ is assumed. A row with no witness gives a nonmember of the projection. This general closure property converts effective stage membership into computable enumerability of a limit set.
-- source:
--   General closure lemma underlying the passage from the recursive finite-stage sequence to its r.e. unions in Arnold W. Miller, Lecture notes in Recursion Theory, December 3, 2008, Section 26, Theorem 26.2, pp. 51–54, https://people.math.wisc.edu/~awmille1/old/m773-07/recthy.pdf#page=51, p. 53. Formal API: Partrec.rfind and Nat.rfind_dom in https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/Partrec.lean; Partrec.dom_re and REPred in https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/RE.lean.

import Mathlib.Computability.RE

namespace FriedbergMuchnik

theorem recursive_projection_re (R : ℕ → ℕ → Prop)
    (hR : ComputablePred (fun p : ℕ × ℕ => R p.1 p.2)) :
    REPred (fun n => ∃ s, R n s) := by sorry

end FriedbergMuchnik
