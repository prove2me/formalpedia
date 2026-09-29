-- Prove2me | Theorems.Thm_LewisTorczon_BoundPS_proposition_4_3_second
-- name    : LewisTorczon.BoundPS.proposition_4_3_second
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:46:59.804569+00:00
-- url     : https://prove2.me/theorems/ceb5577a-c87e-4c05-82e4-f2b531a378e8
-- title:
--   Proposition 4.3, second part — $f(x_{k+1})\le f(x_k)-\sigma\|q(x_k)\|\|s_k\|$ under the Strong Hypotheses
-- statement:
--   Let $x_k,\Delta_k,s_k$ be a run of the generalized pattern search method for the bound constrained problem $\min\{f(x):x\in\Omega\}$. Suppose that $L_\Omega(x_0)$ is compact, that $f$ is continuously differentiable on an open set containing $\Omega$, that the columns of the generating matrices are uniformly bounded in norm, and that the run satisfies the Strong Hypotheses on Bound Constrained Exploratory Moves.
--
--   Then for every $\eta>0$ there are $\delta>0$ and $\sigma>0$, independent of $k$, such that for every $k$ with $\Delta_k<\delta$ and $\|q(x_k)\|>\eta$,
--   $$f(x_{k+1})\le f(x_k)-\sigma\,\|q(x_k)\|\,\|s_k\| .$$
--
--   This sufficient-decrease estimate is what upgrades the $\liminf$ result (Theorem 3.2) to a full limit (Theorem 3.3).
--
--   **Formalization Note** The third Strong Hypothesis is encoded with $f(x_k+s_k)\le f(x_k+y)$ for every feasible core trial step $y$, where the page prints a strict inequality; see the definition file. The smoothness hypothesis is taken on an open set $U\supseteq\Omega$ rather than on $L_\Omega(x_0)$, as for the first part.
-- source:
--   Lewis & Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report No. 96-20 (NASA CR-198306), March 1996, p. 9, Proposition 4.3, second paragraph

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- **Proposition 4.3**, second part, p. 9: if in addition the columns of the generating matrices
are uniformly bounded and the Strong Hypotheses hold, then for every `η > 0` there are `δ > 0`
and `σ > 0`, independent of `k`, such that `Δ_k < δ` and `‖q(x_k)‖ > η` imply
`f(x_{k+1}) ≤ f(x_k) - σ ‖q(x_k)‖ ‖s_k‖`. -/
theorem proposition_4_3_second {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hΩU : box lo hi ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (R : GPSRun n m) (hR : IsGPSRun P lo hi f R)
    (hcpt : IsCompact (levelSet lo hi f (R.x 0))) (hbdd : BoundedCols R)
    (hstrong : StrongHyp P lo hi f R) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ σ : ℝ, 0 < σ ∧
      ∀ k, R.Δ k < δ → η < ‖projQ lo hi f (R.x k)‖ →
        f (R.x (k + 1)) ≤ f (R.x k) - σ * ‖projQ lo hi f (R.x k)‖ * ‖R.s k‖ := by sorry

end LewisTorczon.BoundPS
