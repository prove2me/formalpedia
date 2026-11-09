-- Prove2me | Theorems.Thm_MatroidOptGame_lemma_3
-- name    : MatroidOptGame.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:51:45.088166+00:00
-- url     : https://prove2.me/theorems/f0ecc47e-ece0-4aa1-b415-ed9a4a35068e
-- title:
--   Lemma 3 — the minimum-weight bases are the bases of a matroid $M_w$
-- statement:
--   Let $M = (E, \mathcal I)$ be a finite matroid with weights $w : E \to \mathbb N$, and let $\mathcal B(M, w)$ be the set of minimum-weight bases of $M$. Define
--   $$
--   \mathcal I_w = \{ S : S \subseteq B \text{ for some } B \in \mathcal B(M, w) \}.
--   $$
--   Then $M_w = (E, \mathcal I_w)$ is a matroid.
--
--   MIN's strategy in the case of two disjoint minimum-weight bases (Lemma 5) is Lehman's strategy on $M_w$.
--
--   **Formalization Note** "Is a matroid" is stated as the existence of a Mathlib matroid with the same ground set as $M$ whose independent sets are exactly the members of $\mathcal I_w$.
--
--   Differences from the source:
--   - encoding: the set system M_w = (E, I_w) is a matroid → ∃ N : Matroid α, N.E = M.E ∧ ∀ S, N.Indep S ↔ ∃ B minimum-weight base, S ⊆ B; reason: a matroid is determined by its ground set and independent sets
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.1.1, Lemma 3 and the definition of M_w before it, p.5

import Mathlib
import Definitions.Def_MatroidOptGame_IsMinWeightBase

namespace MatroidOptGame

/-- **Lemma 3.** Let `B(M, w)` be the set of minimum-weight bases of `M` with respect to `w`, and
`I_w = {S : ∃ B ∈ B(M, w), S ⊆ B}`. Then `M_w = (E, I_w)` is a matroid.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.1.1, Lemma 3 and the definition of `M_w` before it, p.5.

**Formalization Note.** "Is a matroid" is stated as: some Mathlib matroid `N` on the same ground
set has exactly the sets of `I_w` as its independent sets. -/
theorem lemma_3 {α : Type*} [Fintype α] (M : Matroid α) (w : α → ℕ) :
    ∃ N : Matroid α, N.E = M.E ∧
      ∀ S : Set α, N.Indep S ↔ ∃ B : Finset α, IsMinWeightBase M w B ∧ S ⊆ (B : Set α) := by sorry

end MatroidOptGame
