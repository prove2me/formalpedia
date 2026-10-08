-- Prove2me | Theorems.Thm_OceanicGames_Limit_theorem_1
-- name    : OceanicGames.Limit.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:11.631169+00:00
-- url     : https://prove2.me/theorems/bcc1cc61-a937-400d-b0c4-65dcf48a3600
-- title:
--   Theorem 1 — oceanic major-player values are limits of finite-game values
-- statement:
--   Consider finite weighted majority games with $m$ major players and $n_\ell$ minor players at stage $\ell$. Let their quota be $c_\ell$, major weights $w_{i,\ell}$, and minor weights $a_{j,\ell}$. All stage weights are nonnegative; the stage quotas are arbitrary real numbers. Let the oceanic game have quota $c\ge0$, nonnegative major weights $w_i$, and ocean weight $\alpha>0$. If
--
--   $$c_\ell\to c,\qquad w_{i,\ell}\to w_i,\qquad \sum_j a_{j,\ell}\to\alpha,\qquad \max_j a_{j,\ell}\to0,$$
--
--   then for every major player $i$,
--
--   $$\phi_{i,\ell}\longrightarrow\phi_i,$$
--
--   where $\phi_{i,\ell}$ is the finite-game Shapley value and $\phi_i$ is the oceanic pivotal probability of (2.4). This is continuity of the values of the major players under increasingly fine division of the minor vote.
--
--   **Formalization Note** Major players precede minor players in the finite player list. Uniform insertion positions are product Lebesgue volume on $[0,1]^m$. The paper's finite weighted majority games are read with nonnegative stage weights, the standing meaning of a weighted majority game; no sign condition is imposed on the stage quotas $c_\ell$, as (3.2) imposes none. The maximum condition has the equivalent eventual-$\varepsilon$ form for nonnegative minor weights, which handles early stages with $n_\ell=0$. No upper bound on the quota is assumed: null games have zero major-player value. The oceanic value remains a pivot probability, not the appendix integral expression.
-- source:
--   Milnor & Shapley, Values of Large Games II: Oceanic Games, RAND RM-2649 (1961), Theorem 1 (3.1)–(3.2), p. 6; https://www.rand.org/pubs/research_memoranda/RM2649.html

import Mathlib
import Definitions.Def_OceanicGames_Limit_Basic

namespace OceanicGames.Limit

open MeasureTheory Set Finset Filter Topology

/-- Theorem 1 (3.1)–(3.2): continuity of the major-player OceanicGames.Interior.value as finite
weighted majority games approximate an oceanic game. -/
theorem theorem_1 {m : ℕ} (c alpha : ℝ) (w : Fin m → ℝ)
    (n : ℕ → ℕ) (cl : ℕ → ℝ) (wl : ℕ → Fin m → ℝ)
    (a : (l : ℕ) → Fin (n l) → ℝ) (i : Fin m)
    (hc : 0 ≤ c) (halpha : 0 < alpha) (hw : ∀ j, 0 ≤ w j)
    (hwl : ∀ l j, 0 ≤ wl l j) (ha : ∀ l j, 0 ≤ a l j)
    (hclim : Tendsto cl atTop (𝓝 c))
    (hwlim : ∀ j, Tendsto (fun l => wl l j) atTop (𝓝 (w j)))
    (halim : Tendsto (fun l => ∑ j, a l j) atTop (𝓝 alpha))
    (hamax : ∀ ε : ℝ, 0 < ε → ∀ᶠ l in atTop, ∀ j, a l j ≤ ε) :
    Tendsto (fun l => finiteValue (cl l) (wl l) (a l) i)
      atTop (𝓝 (OceanicGames.Interior.value c alpha w i)) := by sorry

end OceanicGames.Limit
