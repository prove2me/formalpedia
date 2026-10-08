-- Prove2me | Theorems.Thm_OceanicGames_Interior_eq_4_3
-- name    : OceanicGames.Interior.eq_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:15:25.77103+00:00
-- url     : https://prove2.me/theorems/8b297104-31b0-4c5e-9c07-30eab6fc5e6b
-- title:
--   (4.3), p. 10 — φ_i(y) is the probability that the pivot location F(y) equals x_i
-- statement:
--   Let $\alpha > 0$ and $w_1, \dots, w_m \ge 0$, and let $0 \le y \le w(M) + \alpha$. Write $\varphi_i(y)$ for the value to major player $i$ of the oceanic game $\Gamma(y) = [y; w_1, \dots, w_m; \alpha]$ with quota $y$. For a uniformly random point $x \in I^m$ let
--   $$F(y) = \inf\{ t \ge 0 : w(P(t)) + \alpha t \ge y \}$$
--   be the pivot's location in the ordered ocean, where $P(t) = \{ j : x_j < t \}$. Then, for every $i = 1, \dots, m$,
--   $$\varphi_i(y) = \operatorname{Prob}\{ F(y) = x_i \}.$$
--
--   This recasts the pivot condition (2.4) in terms of the single random function $F$, the starting point of the analysis of §4.
--
--   **Formalization Note** Probabilities are volumes of subsets of $[0,1]^m$. The paper writes $F$ with a minimum; it is read as the infimum over $t \ge 0$ (see the definitions). The quota range $0 \le y \le w(M) + \alpha$ is the domain the paper gives for $F$ in (4.2).
-- source:
--   Milnor & Shapley, Values of Large Games II: Oceanic Games, RAND RM-2649 (1961), §4, (4.3), p. 10

import Mathlib
import Definitions.Def_OceanicGames_Interior_Basic
open MeasureTheory Filter Topology

namespace OceanicGames.Interior

/-- (4.3), p. 10: `φ_i(y) = Prob {F(y) = x_i}` for every quota `0 ≤ y ≤ w(M) + α`. -/
theorem eq_4_3 {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (y : ℝ) (hy0 : 0 ≤ y) (hyW : y ≤ wsum w Finset.univ + α) (i : Fin m) :
    value y α w i = (volume {x | x ∈ cube m ∧ pivotLoc α w x y = x i}).toReal := by sorry

end OceanicGames.Interior
