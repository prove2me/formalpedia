-- Prove2me | Theorems.Thm_MatroidOptGame_theorem_24
-- name    : MatroidOptGame.theorem_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:51:13.1247+00:00
-- url     : https://prove2.me/theorems/c6f8aa6b-f206-4c93-ba94-88eabffa3631
-- title:
--   Theorem 24 — Edmonds' base packing theorem
-- statement:
--   Let $M = (E, \mathcal I)$ be a finite matroid with rank function $r_M$ and let $k \ge 0$ be an integer. Then $M$ has $k$ pairwise disjoint bases if and only if
--   $$
--   |E \setminus F| \;\ge\; k\,\bigl(r_M(E) - r_M(F)\bigr) \qquad \text{for every } F \subseteq E .
--   $$
--   The paper uses this characterization to decide when MAX can force payoff $\infty$ (Lemma 2) and when $M$ has two disjoint bases (Lemma 4).
--
--   **Formalization Note** The $k$ bases are a family indexed by $\{0, \dots, k-1\}$ whose members are pairwise disjoint. The subtraction $r_M(E) - r_M(F)$ is in $\mathbb N$ and exact, since $r_M(F) \le r_M(E)$.
--
--   Differences from the source:
--   - encoding: a matroid M = (E, I) on a finite set E → a Mathlib matroid on a finite type with M.E = Set.univ; reason: every finite matroid is of this form after relabelling its ground set by a type; no instance is lost
--   - encoding: k disjoint bases → a family B : Fin k → Finset α of bases with Pairwise (Disjoint on B); reason: the standard reading of k disjoint bases; for k = 0 both sides hold
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Appendix A, Theorem 24, p.20

import Mathlib
import Definitions.Def_MatroidOptGame_rankOf

namespace MatroidOptGame

/-- **Theorem 24 (Edmonds' base packing theorem).** A matroid `M = (E, I)` has `k` disjoint bases
if and only if for every `F ⊆ E`, `|E ∖ F| ≥ k·(r_M(E) − r_M(F))`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Appendix A, Theorem 24, p.20.

**Formalization Note.** The ground set is the whole finite type (`M.E = Set.univ`); every finite
matroid is of this form after restricting the type to its ground set. "k disjoint bases" is a
family `B : Fin k → Finset α` of bases that are pairwise disjoint. The natural-number subtraction
is exact because `r_M(F) ≤ r_M(E)`. -/
theorem theorem_24 {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α) (hE : M.E = Set.univ)
    (k : ℕ) :
    (∃ B : Fin k → Finset α, (∀ i, M.IsBase (B i : Set α)) ∧ Pairwise fun i j => Disjoint (B i) (B j)) ↔
      ∀ F : Finset α, k * (rankOf M Finset.univ - rankOf M F) ≤ (Finset.univ \ F).card := by sorry

end MatroidOptGame
