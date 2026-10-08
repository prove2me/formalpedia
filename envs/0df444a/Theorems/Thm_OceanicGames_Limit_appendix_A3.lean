-- Prove2me | Theorems.Thm_OceanicGames_Limit_appendix_A3
-- name    : OceanicGames.Limit.appendix_A3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:03.662935+00:00
-- url     : https://prove2.me/theorems/a4339906-9aa6-49db-a2dd-d5c72ee49a60
-- title:
--   Appendix (A.3) — finite weighted majority values converge to the integral expression
-- statement:
--   Consider finite weighted majority games with $m$ major players and $n_\ell$ minor players at stage $\ell$. Let their quota be $c_\ell$, major weights $w_{i,\ell}$, and minor weights $a_{j,\ell}$. All stage weights are nonnegative; the stage quotas are arbitrary real numbers. Suppose
--
--   $$c_\ell\to c\ge0,\qquad w_{i,\ell}\to w_i\ge0,\qquad \sum_j a_{j,\ell}\to\alpha>0,\qquad \max_j a_{j,\ell}\to0.$$
--
--   For every major player $i$, its finite-game Shapley values satisfy
--
--   $$\phi_{i,\ell}\longrightarrow L_i(c,w,\alpha),$$
--
--   where $L_i$ is the coalition sum of integrals in (A.3). The limit is independent of the division of ocean weight among minor players.
--
--   **Formalization Note** Each finite game lists the $m$ majors before the $n_\ell$ minors. The maximum condition is expressed as: for every $\varepsilon>0$, eventually every minor weight is at most $\varepsilon$. Nonnegativity makes this equivalent to the paper's limit even if some early stages have no minor players. This result is a milestone rather than an assumption of Theorem 1.
-- source:
--   Milnor & Shapley, Values of Large Games II: Oceanic Games, RAND RM-2649 (1961), Appendix (A.1)–(A.3), pp. 25–26; https://www.rand.org/pubs/research_memoranda/RM2649.html

import Mathlib
import Definitions.Def_OceanicGames_Limit_Basic

namespace OceanicGames.Limit

open MeasureTheory Set Finset Filter Topology

/-- Appendix (A.1)–(A.3): the finite Shapley values converge to the
integral expression under vanishing maximum minor weight. -/
theorem appendix_A3 {m : ℕ} (c alpha : ℝ) (w : Fin m → ℝ)
    (n : ℕ → ℕ) (cl : ℕ → ℝ) (wl : ℕ → Fin m → ℝ)
    (a : (l : ℕ) → Fin (n l) → ℝ) (i : Fin m)
    (hc : 0 ≤ c) (halpha : 0 < alpha) (hw : ∀ j, 0 ≤ w j)
    (hwl : ∀ l j, 0 ≤ wl l j) (ha : ∀ l j, 0 ≤ a l j)
    (hclim : Tendsto cl atTop (𝓝 c))
    (hwlim : ∀ j, Tendsto (fun l => wl l j) atTop (𝓝 (w j)))
    (halim : Tendsto (fun l => ∑ j, a l j) atTop (𝓝 alpha))
    (hamax : ∀ ε : ℝ, 0 < ε → ∀ᶠ l in atTop, ∀ j, a l j ≤ ε) :
    Tendsto (fun l => finiteValue (cl l) (wl l) (a l) i)
      atTop (𝓝 (limitFormula c alpha w i)) := by sorry

end OceanicGames.Limit
