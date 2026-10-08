-- Prove2me | Theorems.Thm_OceanicGames_Interior_pivotSet_ae_disjoint
-- name    : OceanicGames.Interior.pivotSet_ae_disjoint
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:15:19.954356+00:00
-- url     : https://prove2.me/theorems/03add6e9-b2ad-4b88-8151-6f83f519af19
-- title:
--   §2, p. 5 — the pivot sets A_1, …, A_m are disjoint up to measure zero
-- statement:
--   Consider the oceanic game $[c; w_1, \dots, w_m; \alpha]$ with ocean weight $\alpha > 0$ and nonnegative major-player weights $w_j \ge 0$. For a random point $x \in I^m = [0,1]^m$, let $A_i \subseteq I^m$ be the set on which major player $i$ is pivotal, i.e. on which
--   $$w(P(x_i)) + \alpha x_i \le c \le w(P(x_i)) + w_i + \alpha x_i,$$
--   where $P(t)$ is the set of major players $j$ with $x_j < t$. Then for any two distinct major players $i \ne j$,
--   $$\mu^m(A_i \cap A_j) = 0.$$
--
--   Thus at almost every point of the cube at most one major player is pivotal, which is what makes $\varphi_1 + \dots + \varphi_m \le 1$ and the ocean's value $\Phi = 1 - \sum_i \varphi_i$ nonnegative.
--
--   **Formalization Note** The paper states this as "obviously" true. The Lean statement includes the standing assumptions of §2: $\alpha > 0$, $w_j \ge 0$, and $0 \le c \le w(M)+\alpha$ (the footnote on p. 5).
-- source:
--   Milnor & Shapley, Values of Large Games II: Oceanic Games, RAND RM-2649 (1961), §2, p. 5, last paragraph

import Mathlib
import Definitions.Def_OceanicGames_Interior_Basic
open MeasureTheory Filter Topology

namespace OceanicGames.Interior

/-- §2, p. 5, last paragraph: the pivot sets `A_1, …, A_m` are disjoint up to a set of measure
zero. -/
theorem pivotSet_ae_disjoint {m : ℕ} (c α : ℝ) (w : Fin m → ℝ) (hα : 0 < α)
    (hw : ∀ j, 0 ≤ w j) (hc0 : 0 ≤ c) (hcW : c ≤ wsum w Finset.univ + α)
    (i j : Fin m) (hij : i ≠ j) :
    volume (pivotSet c α w i ∩ pivotSet c α w j) = 0 := by sorry

end OceanicGames.Interior
