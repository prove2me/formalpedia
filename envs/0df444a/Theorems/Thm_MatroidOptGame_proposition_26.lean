-- Prove2me | Theorems.Thm_MatroidOptGame_proposition_26
-- name    : MatroidOptGame.proposition_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:51:56.790789+00:00
-- url     : https://prove2.me/theorems/3a7ddcd4-8da9-4da0-a33c-acc7e6596ba8
-- title:
--   Proposition 26 — $r_{M\vee M}(E) = \min_F\, 2r_M(F) + |E\setminus F|$
-- statement:
--   Let $M = (E, \mathcal I)$ be a finite matroid and $M \vee M$ the union of $M$ with itself. Then:
--   1. for every set $F \subseteq E$,
--   $$
--   r_{M\vee M}(E) \;\le\; 2\, r_M(F) + |E \setminus F| ;
--   $$
--   2. there is a set $F \subseteq E$ for which this inequality is an equality.
--
--   This is the case $k = 2$ of Edmonds' formula $r_{M^k}(E) = \min\{k\,r_M(F) + |E \setminus F| : F \subseteq E\}$ (A.1). The proof of Lemma 7 applies it to the restrictions of $M$ to the sets of elements of weight at most a given value.
--
--   Differences from the source:
--   - encoding: a matroid M = (E, I) on a finite set E → a Mathlib matroid on a finite type with M.E = Set.univ; reason: every finite matroid is of this form after relabelling its ground set by a type; no instance is lost
--   - encoding: the matroid union M ∨ M and its bases → the set system {I ∪ J : I, J independent}; r_{M∨M}(E) its maximum size, B_min(M ∨ M, w) a minimum-weight set of that size; reason: M ∨ M is a matroid (p.20), so its bases are exactly its maximum-size independent sets; Mathlib has no matroid union
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Appendix A, Proposition 26 and Equation (A.1), p.20

import Mathlib
import Definitions.Def_MatroidOptGame_rankOf
import Definitions.Def_MatroidOptGame_unionRank

namespace MatroidOptGame

/-- **Proposition 26.** For any matroid `M = (E, I)` and every `F ⊆ E`,
`r_{M∨M}(E) ≤ 2·r_M(F) + |E ∖ F|`, and some `F ⊆ E` makes this tight.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Appendix A, Proposition 26 (the case `k = 2` of Equation (A.1)), p.20.

**Formalization Note.** `M.E = Set.univ`; `r_{M∨M}(E)` is `unionRank M`, the maximum size of a
union of two independent sets of `M`. -/
theorem proposition_26 {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α)
    (hE : M.E = Set.univ) :
    (∀ F : Finset α, unionRank M ≤ 2 * rankOf M F + (Finset.univ \ F).card) ∧
      ∃ F : Finset α, unionRank M = 2 * rankOf M F + (Finset.univ \ F).card := by sorry

end MatroidOptGame
