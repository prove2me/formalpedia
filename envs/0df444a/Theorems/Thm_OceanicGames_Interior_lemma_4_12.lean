-- Prove2me | Theorems.Thm_OceanicGames_Interior_lemma_4_12
-- name    : OceanicGames.Interior.lemma_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:04.400333+00:00
-- url     : https://prove2.me/theorems/76e1c4da-7b9c-4a74-b909-f90d47f98c58
-- title:
--   Lemma, (4.12)–(4.13), p. 15 — an added major player's value is (1/α)∫Φ(y)dy
-- statement:
--   Let $\alpha > 0$, $w_1, \dots, w_m \ge 0$ and $w_{m+1} \ge 0$. Let $\Gamma(y) = [y; w_1, \dots, w_m; \alpha]$, with ocean value $\Phi(y)$, and let $\Gamma^+(z) = [z; w_1, \dots, w_m, w_{m+1}; \alpha]$ be the game with an added major player $m+1$, whose value there is $\varphi^+_{m+1}(z)$. For $0 \le z \le w(M) + w_{m+1} + \alpha$ put
--   $$t_1 = \max(z - w_{m+1}, 0), \qquad t_2 = \min(z, w(M) + \alpha). \qquad (4.11)$$
--   Then
--   $$\varphi^+_{m+1}(z) = \frac{1}{\alpha} \int_{t_1}^{t_2} \Phi(y)\, dy. \qquad (4.12)$$
--   If moreover $w_{m+1} \le z \le w(M) + \alpha$ (condition (4.10)), this reduces to
--   $$\varphi^+_{m+1}(z) = \frac{1}{\alpha} \int_{z - w_{m+1}}^{z} \Phi(y)\, dy. \qquad (4.13)$$
--
--   The lemma expresses a new player's value through the ocean values of the smaller games; iterating it computes values player by player, which is how the interior formulas of §5 are obtained.
--
--   **Formalization Note** The added player is appended to the weight vector with `Fin.snoc`, as index `Fin.last m`. The range of $z$ is the one stated on p. 14 before (4.9). The integrals are interval integrals over $[t_1, t_2]$; in this range $t_1 \le t_2$.
-- source:
--   Milnor & Shapley, Values of Large Games II: Oceanic Games, RAND RM-2649 (1961), §4, Lemma, (4.10)–(4.13), pp. 14–15

import Mathlib
import Definitions.Def_OceanicGames_Interior_Basic
open MeasureTheory Filter Topology

namespace OceanicGames.Interior

/-- Lemma, (4.11)–(4.13), pp. 14–15: the value of an added major player `m+1` of weight `w'` in
`Γ⁺(z)` is `(1/α) ∫_{t_1}^{t_2} Φ(y) dy`, `t_1 = max (z − w', 0)`, `t_2 = min (z, w(M) + α)`, for
`0 ≤ z ≤ w(M) + w' + α`; under (4.10) `w' ≤ z ≤ w(M) + α` it is `(1/α) ∫_{z−w'}^{z} Φ(y) dy`. -/
theorem lemma_4_12 {m : ℕ} (α w' : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (hw' : 0 ≤ w') (z : ℝ) (hz0 : 0 ≤ z) (hzW : z ≤ wsum w Finset.univ + w' + α) :
    value z α (addWeight w w') (Fin.last m) =
        1 / α * ∫ y in (max (z - w') 0)..(min z (wsum w Finset.univ + α)), oceanValue y α w ∧
    (w' ≤ z → z ≤ wsum w Finset.univ + α →
      value z α (addWeight w w') (Fin.last m) =
        1 / α * ∫ y in (z - w')..z, oceanValue y α w) := by sorry

end OceanicGames.Interior
