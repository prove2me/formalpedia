-- Prove2me | Theorems.Thm_OceanicGames_Interior_theorem_6_efficiency
-- name    : OceanicGames.Interior.theorem_6_efficiency
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:02.246517+00:00
-- url     : https://prove2.me/theorems/8380e497-ec6d-4db9-9943-5866c890a3ad
-- title:
--   Proof of Theorem 6, p. 21 — the formulas (5.9) and (5.10) satisfy (2.5)
-- statement:
--   Let $\alpha \ne 0$ and $w_1, \dots, w_m$ be real numbers, $M = \{1, \dots, m\}$, $\bar w_j = \alpha - w_j$, and let $a_0 = 1$, $a_n = 1 - n a_{n-1}$. For $S \subseteq M$ let $\pi(S) = \prod_{j \in S} \frac{w_j}{\alpha} \prod_{j \in M - S} \frac{\bar w_j}{\alpha}$, and for $S \subseteq M - \{i\}$ let $\pi_i(S)$ be the same product over $M - \{i\}$. Writing $s = |S|$,
--   $$\sum_{i \in M} \frac{w_i}{\alpha} \sum_{S \subseteq M - \{i\}} a_s \, \pi_i(S) \;=\; 1 - \sum_{S \subseteq M} a_s \, \pi(S).$$
--
--   This is the algebraic step of the induction proving Theorem 6: the closed-form major-player values (5.9) and ocean value (5.10) add up to 1, as (2.5) requires.
--
--   **Formalization Note** This is a pure identity between polynomials in $w_j / \alpha$; it needs only $\alpha \ne 0$, and no sign or interior condition.
-- source:
--   Milnor & Shapley, Values of Large Games II: Oceanic Games, RAND RM-2649 (1961), proof of Theorem 6, p. 21

import Mathlib
import Definitions.Def_OceanicGames_Interior_Basic
open MeasureTheory Filter Topology

namespace OceanicGames.Interior

/-- Proof of Theorem 6, p. 21: the formulas (5.9) and (5.10) satisfy (2.5), i.e.
`Σ_{i∈M} (w_i/α) Σ_{S⊆M−{i}} a_s π_i(S) = 1 − Σ_{S⊆M} a_s π(S)` (an algebraic identity). -/
theorem theorem_6_efficiency {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : α ≠ 0) :
    ∑ i, w i / α * ∑ S ∈ (Finset.univ.erase i).powerset, (coeff S.card : ℝ) * piProdErase α w i S
      = 1 - ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset, (coeff S.card : ℝ) * piProd α w S := by sorry

end OceanicGames.Interior
