-- Prove2me | Theorems.Thm_OceanicGames_Interior_theorem_6
-- name    : OceanicGames.Interior.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:12.912054+00:00
-- url     : https://prove2.me/theorems/b3c6ab3d-b42e-4456-b89b-c2c38270f20d
-- title:
--   Theorem 6 — closed-form values of interior oceanic games: φ_i = (w_i/α) Σ a_s π_i(S), Φ = Σ a_s π(S)
-- statement:
--   Let $\alpha > 0$ and $w_1, \dots, w_m \ge 0$, and let the oceanic game $[c; w_1, \dots, w_m; \alpha]$ be interior:
--   $$w(M) \le c \le \alpha.$$
--   Let $a_0 = 1$, $a_n = 1 - n a_{n-1}$ (so $a_n = 1, 0, 1, -2, 9, -44, \dots$), let $\bar w_j = \alpha - w_j$, let $\pi(S) = \prod_{j \in S} \frac{w_j}{\alpha} \prod_{j \in M - S} \frac{\bar w_j}{\alpha}$ for $S \subseteq M$, and let $\pi_i(S) = \prod_{j \in S} \frac{w_j}{\alpha} \prod_{j \in (M - \{i\}) - S} \frac{\bar w_j}{\alpha}$ for $S \subseteq M - \{i\}$. Writing $s$ for the number of elements of $S$, the value to the $i$-th major player is
--   $$\varphi_i = \frac{w_i}{\alpha} \sum_{S \subseteq M - \{i\}} a_s \, \pi_i(S), \qquad (5.9)$$
--   and the combined value of the ocean is
--   $$\Phi = \sum_{S \subseteq M} a_s \, \pi(S). \qquad (5.10)$$
--
--   Here $\varphi_i$ is the probability that player $i$ is pivotal when the major players are inserted at independent uniform positions of the ocean, and $\Phi = 1 - \sum_i \varphi_i$. The theorem gives these values in closed form; in particular they do not depend on the quota $c$ within the interior range. For $m = 1$ it gives $\varphi_1 = w_1/\alpha$ and $\Phi = \bar w_1 / \alpha$.
--
--   **Formalization Note** $\varphi_i$ is the Lebesgue volume of the pivot set (2.4) in $[0,1]^m$, and $\Phi$ is defined by (2.5); neither is defined through these formulas. $\alpha > 0$ and $w_j \ge 0$ are the standing assumptions of §2. $a_s$ is an integer cast to the reals.
-- source:
--   Milnor & Shapley, Values of Large Games II: Oceanic Games, RAND RM-2649 (1961), Theorem 6, (5.9)–(5.10), p. 20

import Mathlib
import Definitions.Def_OceanicGames_Interior_Basic
open MeasureTheory Filter Topology

namespace OceanicGames.Interior

/-- Theorem 6, (5.9)–(5.10), p. 20: in the interior oceanic game `[c; w_1, …, w_m; α]`,
`w(M) ≤ c ≤ α`, `φ_i = (w_i/α) Σ_{S⊆M−{i}} a_s π_i(S)` and `Φ = Σ_{S⊆M} a_s π(S)`. -/
theorem theorem_6 {m : ℕ} (c α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (hint : IsInterior c α w) :
    (∀ i, value c α w i =
      w i / α * ∑ S ∈ (Finset.univ.erase i).powerset, (coeff S.card : ℝ) * piProdErase α w i S) ∧
    oceanValue c α w =
      ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset, (coeff S.card : ℝ) * piProd α w S := by sorry

end OceanicGames.Interior
