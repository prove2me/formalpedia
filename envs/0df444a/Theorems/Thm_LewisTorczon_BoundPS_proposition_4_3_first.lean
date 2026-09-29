-- Prove2me | Theorems.Thm_LewisTorczon_BoundPS_proposition_4_3_first
-- name    : LewisTorczon.BoundPS.proposition_4_3_first
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:46:31.233519+00:00
-- url     : https://prove2.me/theorems/3a7c8d66-fdcb-4679-8a20-de1369675fdf
-- title:
--   Proposition 4.3, first part — if $\Delta_k<\delta$ and $\|q(x_k)\|>\eta$ the method finds an acceptable step
-- statement:
--   Let $x_k,\Delta_k,s_k$ be a run of the generalized pattern search method for the bound constrained problem $\min\{f(x):x\in\Omega\}$. Suppose that $L_\Omega(x_0)=\{x\in\Omega:f(x)\le f(x_0)\}$ is compact and that $f$ is continuously differentiable on an open set containing $\Omega$.
--
--   Then for every $\eta>0$ there is $\delta>0$, independent of $k$, such that for every $k$,
--   $$\Delta_k<\delta\ \text{ and }\ \|q(x_k)\|>\eta\quad\Longrightarrow\quad f(x_k+s_k)<f(x_k)\ \text{ and }\ x_k+s_k\in\Omega .$$
--
--   In words: away from stationarity, a small enough step length always yields a successful iteration, so the step length cannot be contracted indefinitely there.
--
--   **Formalization Note** The page assumes $f$ continuously differentiable on $L_\Omega(x_0)$; the statement assumes it on an open set $U\supseteq\Omega$, because the argument evaluates $\nabla f$ along segments to trial points that lie in $\Omega$ but generally outside $L_\Omega(x_0)$. $\delta$ is chosen before $k$ ("independent of $k$").
-- source:
--   Lewis & Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report No. 96-20 (NASA CR-198306), March 1996, p. 9, Proposition 4.3, first paragraph

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- **Proposition 4.3**, first part, p. 9: if `L_Ω(x_0)` is compact and `f` is `C¹`, then for every
`η > 0` there is `δ > 0`, independent of `k`, such that `Δ_k < δ` and `‖q(x_k)‖ > η` imply that
the method finds an acceptable step: `f(x_k + s_k) < f(x_k)` and `x_k + s_k ∈ Ω`. -/
theorem proposition_4_3_first {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hΩU : box lo hi ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (R : GPSRun n m) (hR : IsGPSRun P lo hi f R)
    (hcpt : IsCompact (levelSet lo hi f (R.x 0))) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ k, R.Δ k < δ → η < ‖projQ lo hi f (R.x k)‖ →
      f (R.x k + R.s k) < f (R.x k) ∧ R.x k + R.s k ∈ box lo hi := by sorry

end LewisTorczon.BoundPS
