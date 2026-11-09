-- Prove2me | Theorems.Thm_MatroidOptGame_proposition_27
-- name    : MatroidOptGame.proposition_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:49:47.009535+00:00
-- url     : https://prove2.me/theorems/ac0ad855-b643-484c-bd15-d01652cb5ae5
-- title:
--   Proposition 27 — $B\setminus\{e\}$ is a base of $M/e$
-- statement:
--   Let $B$ be a base of a matroid $M$ and let $e \in B$. Then $B \setminus \{e\}$ is a base of the contraction $M / e$.
--
--   The proof of Lemma 5 uses it to see that the invariant "two disjoint minimum-weight bases" survives a round of play.
--
--   **Formalization Note** Contraction is Mathlib's `Matroid.contract` by the singleton $\{e\}$. The statement is for an arbitrary Mathlib matroid.
--
--   Differences from the source: none.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Appendix A, Proposition 27, p.21

import Mathlib

namespace MatroidOptGame

/-- **Proposition 27.** Let `B` be a base of `M` and `e ∈ B`. Then `B ∖ {e}` is a base of `M / e`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Appendix A, Proposition 27, p.21. The `/` here is contraction (Appendix A,
p.19).

**Formalization Note.** Mathlib's contraction `M.contract {e}` (`M ／ {e}`); no finiteness or ground-set assumption
is needed. -/
theorem proposition_27 {α : Type*} (M : Matroid α) (B : Set α) (e : α) (hB : M.IsBase B)
    (he : e ∈ B) : (M.contract {e}).IsBase (B \ {e}) := by sorry

end MatroidOptGame
