-- Prove2me | Theorems.Thm_OceanicGames_Interior_theorem_5
-- name    : OceanicGames.Interior.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:16:56.53422+00:00
-- url     : https://prove2.me/theorems/927d9585-5429-4938-8c73-4a7596c06cfa
-- title:
--   Theorem 5 — in interior oceanic games an added major player's value is (1/α)·Φ·w_{m+1}
-- statement:
--   Let $\alpha > 0$, $w_1, \dots, w_m \ge 0$ and $w_{m+1} \ge 0$. Suppose that the oceanic games
--   $$\Gamma = [c; w_1, \dots, w_m; \alpha] \quad\text{and}\quad \Gamma^+ = [d; w_1, \dots, w_{m+1}; \alpha]$$
--   are both interior, i.e. $w_1 + \dots + w_m \le c \le \alpha$ and $w_1 + \dots + w_{m+1} \le d \le \alpha$. Then the value of the added player $m+1$ in $\Gamma^+$ is
--   $$\varphi^+_{m+1} = \frac{1}{\alpha} \, \Phi \, w_{m+1}, \qquad (5.4)$$
--   where $\Phi$ is the combined value of the ocean in $\Gamma$.
--
--   The quotas $c$ and $d$ are independent, so the theorem includes the fact that in an interior game the values do not depend on the quota. Together with (2.5) it determines all interior values recursively.
--
--   **Formalization Note** The added player is appended with `Fin.snoc` as index `Fin.last m`; $\Phi = 1 - \sum_i \varphi_i$ by (2.5).
-- source:
--   Milnor & Shapley, Values of Large Games II: Oceanic Games, RAND RM-2649 (1961), Theorem 5, (5.4), p. 18

import Mathlib
import Definitions.Def_OceanicGames_Interior_Basic
open MeasureTheory Filter Topology

namespace OceanicGames.Interior

/-- Theorem 5, (5.4), p. 18: if `Γ = [c; w_1, …, w_m; α]` and `Γ⁺ = [d; w_1, …, w_{m+1}; α]` are
both interior, then `φ⁺_{m+1} = (1/α) Φ w_{m+1}`. -/
theorem theorem_5 {m : ℕ} (c d α w' : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (hw' : 0 ≤ w') (hΓ : IsInterior c α w) (hΓ' : IsInterior d α (addWeight w w')) :
    value d α (addWeight w w') (Fin.last m) = 1 / α * oceanValue c α w * w' := by sorry

end OceanicGames.Interior
