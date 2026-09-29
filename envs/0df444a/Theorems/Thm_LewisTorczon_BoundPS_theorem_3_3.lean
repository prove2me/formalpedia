-- Prove2me | Theorems.Thm_LewisTorczon_BoundPS_theorem_3_3
-- name    : LewisTorczon.BoundPS.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:49:05.648529+00:00
-- url     : https://prove2.me/theorems/d79b2679-d345-4fde-9589-7fe87d456864
-- title:
--   Theorem 3.3 — $\lim_{k\to\infty}\|q(x_k)\|=0$ under the Strong Hypotheses
-- statement:
--   Consider the bound constrained problem $\min\{f(x):\ell\le x\le u\}$ on $\Omega=\{\ell\le x\le u\}$, with $\ell_j<u_j$ for every $j$ (infinite bounds allowed), and let $q(x)=P(x-\nabla f(x))-x$, where $P$ is the projection onto $\Omega$. Let $x_k,\Delta_k,s_k,C_k$ be a run of the generalized pattern search method for bound constrained minimization (Algorithm 1 with Algorithm 2). Suppose that
--   1. $L_\Omega(x_0)=\{x\in\Omega:f(x)\le f(x_0)\}$ is compact;
--   2. $f$ is continuously differentiable on an open set containing $\Omega$;
--   3. the columns of the generating matrices $C_k$ are uniformly bounded in norm;
--   4. $\lim_{k\to\infty}\Delta_k=0$;
--   5. the run enforces the Strong Hypotheses on Bound Constrained Exploratory Moves.
--
--   Then
--   $$\lim_{k\to\infty}\|q(x_k)\|=0 .$$
--
--   Since $q(x)=0$ exactly at stationary points of the bound constrained problem, every limit point of the iterates is then a stationary point: the whole sequence, not just a subsequence, approaches first-order stationarity.
--
--   **Formalization Note** Two departures from the page, both disclosed in the mission description. (i) The page assumes $f$ continuously differentiable on $L_\Omega(x_0)$; here it is assumed on an open set $U\supseteq\Omega$, which the proof needs (it uses $\nabla f$ at trial points in $\Omega$ outside $L_\Omega(x_0)$, and $L_\Omega(x_0)$ may have empty interior). (ii) The third Strong Hypothesis is encoded with "$\le$" instead of the printed "$<$" (the printed strict form excludes the paper's own examples; "$\le$" is the weaker hypothesis). Norms are Euclidean.
-- source:
--   Lewis & Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report No. 96-20 (NASA CR-198306), March 1996, p. 7, Theorem 3.3 (proof in §4.2, p. 11)

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- **Theorem 3.3**, p. 7: if `L_Ω(x_0)` is compact, `f` is `C¹`, the columns of the generating
matrices are uniformly bounded in norm, `Δ_k → 0`, and the method enforces the Strong Hypotheses
on Bound Constrained Exploratory Moves, then `‖q(x_k)‖ → 0`. -/
theorem theorem_3_3 {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hΩU : box lo hi ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (R : GPSRun n m) (hR : IsGPSRun P lo hi f R)
    (hcpt : IsCompact (levelSet lo hi f (R.x 0))) (hbdd : BoundedCols R)
    (hΔ : Filter.Tendsto R.Δ Filter.atTop (nhds 0)) (hstrong : StrongHyp P lo hi f R) :
    Filter.Tendsto (fun k => ‖projQ lo hi f (R.x k)‖) Filter.atTop (nhds 0) := by sorry

end LewisTorczon.BoundPS
