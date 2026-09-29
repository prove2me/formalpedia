-- Prove2me | Theorems.Thm_OnlineConvexOpt_Blackwell_blackwell_approachability_sufficiency
-- name    : OnlineConvexOpt.Blackwell.blackwell_approachability_sufficiency
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:52:59.205994+00:00
-- url     : https://prove2.me/theorems/17b0c249-9710-45d4-b9ac-e025d4f4e86d
-- title:
--   Theorem 13.4 — Blackwell's Approachability Theorem, sufficiency direction (goal)
-- statement:
--   **Statement (Theorem 13.4, p. 209, PDF p. 231; sufficiency direction only — see
--   Formalization Note).** For any vector game $K_1,K_2,u$ with both players' decision sets
--   nonempty, if $\forall y\in K_2,\exists x\in K_1, u(x,y)\in S$, then the closed, bounded,
--   convex set $S$ is approachable.
--
--   Blackwell's theorem, in its full generality over arbitrary vector games (not just discrete
--   strategy sets as in Blackwell's original 1956 paper), characterizing exactly which sets are
--   approachable via a purely geometric best-response condition — no reference to any specific
--   algorithm.
--
--   **Formalization Note.** The book's own theorem is stated as a biconditional, but its text
--   says explicitly: "The necessity of this condition is left as an exercise, and the more
--   interesting implication is that any set that satisfies this condition is, in fact,
--   approachable. Our reductions henceforth give an explicit proof of Blackwell's theorem" —
--   only the sufficiency direction (the $\leftarrow$ of the book's $\iff$) has a proof on these
--   pages, so only that direction is drafted, per `CAPTAIN_BRIEF.md` rule 6 and `BRIEF.md`'s
--   explicit scope instruction. Drafting the full `↔` here would misrepresent what the book
--   actually establishes.
--
--
--   **Revision (2026-09-19).** A moderator change request found the theorem false as
--   originally stated: with $K_1=\emptyset$, $K_2=\emptyset$ (both vacuously bounded, closed,
--   convex), `hcond` holds vacuously, but `IsApproachable K1 K2 u S`'s first conjunct requires
--   `Astrat y t ∈ K1` for *every* `y : ℕ → E2` and `t ≥ 1` — impossible when $K_1=\emptyset$, so
--   the theorem instantiated to `True → False`. Added `hK1ne : K1.Nonempty` and
--   `hK2ne : K2.Nonempty`, matching Definition 13.2's implicit reading of "two players'
--   decision sets."
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 209, Theorem 13.4 (PDF p. 231)

import Mathlib
import Definitions.Def_OnlineConvexOpt_Blackwell_Approachability

namespace OnlineConvexOpt.Blackwell

/-- Theorem 13.4, Blackwell's Approachability Theorem — **sufficiency direction only** (Hazan,
*Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, p. 209, PDF p. 231).
For any vector game `K1, K2, u` with both players' decision sets nonempty, if
`∀y∈K2, ∃x∈K1, u(x,y)∈S`, then the closed, bounded, convex set `S` is approachable.

The book's own theorem is a biconditional ("the closed, bounded and convex set `S` is
approachable if and only if..."), but states explicitly: "The necessity of this condition is
left as an exercise, and the more interesting implication is that any set that satisfies this
condition is, in fact, approachable. Our reductions henceforth give an explicit proof of
Blackwell's theorem" — the book proves, and this mission drafts, only the sufficiency direction
(the `↔`'s `←`), per `CAPTAIN_BRIEF.md` rule 6 (a result may only be drafted to the extent its
hypotheses/proof are actually pinned down on the page) and `BRIEF.md`'s explicit scope
instruction; see `STATUS.md`. -/
theorem blackwell_approachability_sufficiency
    {E1 E2 F : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E2]
    [NormedSpace ℝ E2] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K1 : Set E1) (K2 : Set E2) (u : E1 → E2 → F) (S : Set F)
    (hSconv : Convex ℝ S) (hSbdd : Bornology.IsBounded S) (hSclosed : IsClosed S)
    (hK1bdd : Bornology.IsBounded K1) (hK1closed : IsClosed K1) (hK1conv : Convex ℝ K1)
    (hK2bdd : Bornology.IsBounded K2) (hK2closed : IsClosed K2) (hK2conv : Convex ℝ K2)
    (hK1ne : K1.Nonempty) (hK2ne : K2.Nonempty)
    (hcond : ∀ y ∈ K2, ∃ x ∈ K1, u x y ∈ S) :
    IsApproachable K1 K2 u S := by sorry

end OnlineConvexOpt.Blackwell
