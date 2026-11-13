-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_lemma_4_4
-- name    : LowDiameterNashWilliams.Main.lemma_4_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:49.117072+00:00
-- url     : https://prove2.me/theorems/d7f47f08-ef79-4adf-8854-3d99005dea18
-- title:
--   Lemma 4.4 — Sampling a perfect matching
-- statement:
--   Let $B$ be a simple bipartite graph whose two classes have size $m\ge2$, with minimum degrees $\delta_L,\delta_R$ satisfying $\delta_L+\delta_R\ge5m/4$. Then $B$ has a perfect matching.
--
--   Independently at each right vertex $j$, choose an arbitrary random subset $S_j\subseteq N_B(j)$. If $p\in(0,1]$ and
--
--   $$\Pr(S_j\cap X=\varnothing)\le\exp(-p|X|)\quad(j\in R,\ X\subseteq N_B(j)),\qquad pm\ge96\log m,$$
--
--   then the graph with right neighborhoods $S_j$ satisfies
--
--   $$\Pr(B'\text{ has a perfect matching})\ge1-4m^{-11}.$$
--
--   The laws concern whole subsets and are only required to be independent between right vertices. This gives both deterministic restoration and its sampled-head estimate.
--
--   Differences from the source:
--   - encoding: two vertex classes of size m and arbitrary independent neighbor-subset laws → both classes Fin m, PMFs on finite subsets, joint event probability as the finite sum of products of marginal masses; reason: all finite subset laws are represented, without adding within-subset independence or restricting to a sampling scheme
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Lemma 4.4, p. 16 (PDF p. 17)

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Geometry
import Definitions.Def_LowDiameterNashWilliams_Main_Reserves
import Definitions.Def_LowDiameterNashWilliams_Main_Sampling
import Definitions.Def_LowDiameterNashWilliams_Main_Computation

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main

theorem lemma_4_4 :
  ∀ m : ℕ, 2 ≤ m → ∀ N : Fin m → Finset (Fin m),
  (5 : ℝ) * m / 4 ≤ (leftMin N : ℝ) + rightMin N →
  PerfectMatching N ∧
  ∀ (μ : Fin m → PMF (Finset (Fin m))) (p : ℝ), 0 < p → p ≤ 1 →
    (∀ j S, μ j S ≠ 0 → S ⊆ N j) →
    (∀ j X, X ⊆ N j → avoidance (μ j) X ≤ ENNReal.ofReal (Real.exp (-p * X.card))) →
    96 * Real.log m ≤ p * m →
    ENNReal.ofReal (1 - 4 * (m : ℝ) ^ (-(11 : ℤ))) ≤ matchingProbability μ := by sorry

end LowDiameterNashWilliams.Main
