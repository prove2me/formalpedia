-- Prove2me | Theorems.Thm_MatroidOptGame_lemma_7
-- name    : MatroidOptGame.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:57:39.185385+00:00
-- url     : https://prove2.me/theorems/5c6f0288-bd19-4e52-ae26-36b9dfcfc424
-- title:
--   Lemma 7 — MAX guarantees payoff $\tfrac12(w(B_1)+w(B_2))$ for a minimum disjoint pair
-- statement:
--   Let $M$ be a finite matroid with weights $w : E \to \mathbb N$, and let $B_1, B_2$ be disjoint bases of $M$ minimizing $w(B_1) + w(B_2)$ over all pairs of disjoint bases. Then MAX has a legal strategy $c$ such that, against every legal MIN strategy $s$,
--   $$
--   p(c, s) \;\ge\; \tfrac12\bigl(w(B_1) + w(B_2)\bigr).
--   $$
--   The bound is on MAX's payoff itself, not on the excess payoff. Combined with $w(B_1) + w(B_2) = w(B_{\min}(M \vee M, w))$ it gives MAX's half of Theorem 1.
--
--   **Formalization Note** The statement has no efficiency clause; the efficient version of MAX's strategy is part of Theorem 1.
--
--   Differences from the source:
--   - encoding: a matroid M = (E, I) on a finite set E → a Mathlib matroid on a finite type with M.E = Set.univ; reason: every finite matroid is of this form after relabelling its ground set by a type; no instance is lost
--   - reading: pure strategies as functions of the positive-rank minors of M → strategies as functions of the history of moves (List → Option), legal at every live position of the player's turn; reason: a minor forgets which elements were deleted and which contracted, the paper's efficient strategies are defined along the play, and the value is the same for both strategy spaces (finite perfect-information game, backward induction)
--   - encoding: payoffs, values, δ and Δ in ℕ ∪ {∞} or ℝ ∪ {∞} → payoff and value in ℕ∞, δ, Δ and excess payoffs in EReal (2·⊤ = ⊤, ⊤ − x = ⊤); reason: Lean convention; the ∞ cases are represented, not excluded
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Lemma 7, p.9

import Mathlib
import Definitions.Def_MatroidOptGame_weight
import Definitions.Def_MatroidOptGame_Strategy
import Definitions.Def_MatroidOptGame_LegalMax
import Definitions.Def_MatroidOptGame_LegalMin
import Definitions.Def_MatroidOptGame_payoff
import Definitions.Def_NKtLB_toEReal

namespace MatroidOptGame

/-- **Lemma 7.** Let `B₁, B₂` be a pair of disjoint bases of `M` that minimize `w(B₁) + w(B₂)`.
Then MAX can guarantee a payoff of at least `½(w(B₁) + w(B₂))`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Lemma 7, p.9.

**Formalization Note.** `M.E = Set.univ`; strategies on histories. The bound is on the payoff
itself, not on the excess payoff. "Minimize" is over all pairs of disjoint bases. The statement
has no efficiency clause (the efficient MAX strategy of its proof is part of Theorem 1). -/
theorem lemma_7 {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α) (hE : M.E = Set.univ)
    (w : α → ℕ) (B₁ B₂ : Finset α) (hB₁ : M.IsBase (B₁ : Set α)) (hB₂ : M.IsBase (B₂ : Set α))
    (hdisj : Disjoint B₁ B₂)
    (hmin : ∀ B₁' B₂' : Finset α, M.IsBase (B₁' : Set α) → M.IsBase (B₂' : Set α) →
      Disjoint B₁' B₂' → weight w B₁ + weight w B₂ ≤ weight w B₁' + weight w B₂') :
    ∃ c : Strategy α, LegalMax M c ∧ ∀ s : Strategy α, LegalMin M s →
      ((((weight w B₁ + weight w B₂ : ℕ) : ℝ) / 2 : ℝ) : EReal) ≤ NKtLB.toEReal (payoff M w c s) := by sorry

end MatroidOptGame
