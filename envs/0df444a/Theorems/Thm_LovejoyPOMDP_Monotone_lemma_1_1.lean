-- Prove2me | Theorems.Thm_LovejoyPOMDP_Monotone_lemma_1_1
-- name    : LovejoyPOMDP.Monotone.lemma_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:39:35.849257+00:00
-- url     : https://prove2.me/theorems/d72fb9e8-47fd-473d-9df0-f511855492f8
-- title:
--   Lemma 1.1 — π ≥s π′ iff every nondecreasing f has larger expectation under π
-- statement:
--   Let $X$ be a finite, completely ordered set and let $\pi,\pi'\in\Pi(X)$. Then $\pi\ge_s\pi'$ if and only if
--   $$\sum_{i\in X}\pi'_i f(i)\ \le\ \sum_{i\in X}\pi_i f(i)\qquad\text{for every nondecreasing } f:X\to\mathbb R.$$
--
--   This is the standard characterization of first-order stochastic dominance (Stoyan 1983). In the paper it is the tool that turns stochastic dominance of beliefs or observation distributions into inequalities between expected values.
--
--   **Formalization Note** The paper says "countable" but works with a finite set $X$ of $n$ elements (§1), so the lemma is stated for a finite chain. The printed "$\Pi'\le_s\pi$" is a typo for $\pi'\le_s\pi$.
-- source:
--   Lovejoy, Some Monotonicity Results for Partially Observed Markov Decision Processes, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 737, Lemma 1.1

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Orders

namespace LovejoyPOMDP.Monotone

/-- Lovejoy, *Some Monotonicity Results for Partially Observed Markov Decision Processes*, Oper. Res. 35(5):736–743 (1987), DOI 10.1287/opre.35.5.736, p. 737, Lemma 1.1.

For `π, π' ∈ Π(X)` on a finite chain `X`: `π ≥s π'` if and only if
`Σ_i π'_i f(i) ≤ Σ_i π_i f(i)` for every nondecreasing `f : X → ℝ`.

**Formalization Note.** The paper says "countable" but sums to `n` and has fixed `X` finite in §1;
the lemma is stated for a finite chain. The paper's "`Π' ≤s π`" is a typo for `π' ≤s π`. -/
theorem lemma_1_1 {X : Type*} [Fintype X] [LinearOrder X] {π π' : X → ℝ}
    (hπ : π ∈ stdSimplex ℝ X) (hπ' : π' ∈ stdSimplex ℝ X) :
    StochGE π π' ↔ ∀ f : X → ℝ, Monotone f → ∑ i, π' i * f i ≤ ∑ i, π i * f i := by sorry

end LovejoyPOMDP.Monotone
