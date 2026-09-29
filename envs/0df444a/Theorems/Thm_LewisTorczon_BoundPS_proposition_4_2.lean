-- Prove2me | Theorems.Thm_LewisTorczon_BoundPS_proposition_4_2
-- name    : LewisTorczon.BoundPS.proposition_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:46:00.553675+00:00
-- url     : https://prove2.me/theorems/710798f9-7f4e-444d-b94e-037b44224549
-- title:
--   Proposition 4.2 — a feasible core trial step with $g_k^Ts_k^i\le-n^{-1/2}\|q_k\|\|s_k^i\|$
-- statement:
--   Let $x_k,\Delta_k,C_k=[M_k\ {-M_k}\ L_k]$ be a run of the generalized pattern search method for the bound constrained problem $\min\{f(x):x\in\Omega\}$, with $f$ continuously differentiable on an open set containing $\Omega$. Write $g_k=\nabla f(x_k)$, $q_k=q(x_k)$ and $\Gamma_k=[M_k\ {-M_k}]$, and suppose $q_k\ne0$.
--
--   Then there is $\nu_k>0$ such that, whenever the step length satisfies $0<\Delta<\nu_k$, some column $c$ of $\Gamma_k$ gives a trial step $s=\Delta Bc$ with $x_k+s\in\Omega$ and
--   $$g_k^{T}s\le-c_n\,\|q_k\|\,\|s\|,\qquad c_n=n^{-1/2}.$$
--
--   The proposition is where the bound constrained case departs from the unconstrained one: because $BM_k$ is diagonal, the core pattern contains coordinate directions, and one of them is simultaneously feasible and a uniformly good descent direction as measured by $q_k$.
--
--   **Formalization Note** $\nu_k$ depends on the iteration $k$ (through $x_k$ and $M_k$) but not on the step length, so the statement quantifies over every step length $0<\Delta<\nu_k$ rather than referring to the run's own $\Delta_k$; with $\Delta_k$ fixed, "there is $\nu_k$ with $\Delta_k<\nu_k\Rightarrow\dots$" would be satisfied vacuously by $\nu_k=\Delta_k$. The paper's proof applies it with $\Delta=\Delta_k$. The page assumes $f$ continuously differentiable on $L_\Omega(x_0)$; the mission assumes it on an open set $U\supseteq\Omega$ throughout (see the mission description). At $n=0$ one always has $q_k=0$, so no division by zero arises. Norms are Euclidean.
-- source:
--   Lewis & Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report No. 96-20 (NASA CR-198306), March 1996, p. 8, Proposition 4.2

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- **Proposition 4.2**, p. 8. If `q(x_k) ≠ 0`, there is `ν_k > 0` (depending on the iteration `k`
through `x_k` and `M_k`, but not on the step length) such that for every step length
`0 < Δ < ν_k` some column `c` of `Γ_k = [M_k  -M_k]` gives a trial step `s = Δ B c` with
`x_k + s ∈ Ω` and `g_kᵀ s ≤ -c_n ‖q_k‖ ‖s‖`, `c_n = n^{-1/2}`. -/
theorem proposition_4_2 {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hΩU : box lo hi ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (R : GPSRun n m) (hR : IsGPSRun P lo hi f R) (k : ℕ)
    (hq : projQ lo hi f (R.x k) ≠ 0) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ Δ : ℝ, 0 < Δ → Δ < ν →
      ∃ c ∈ coreCols R k, R.x k + stepOf P Δ c ∈ box lo hi ∧
        inner ℝ (gradient f (R.x k)) (stepOf P Δ c) ≤
          -(1 / Real.sqrt n) * ‖projQ lo hi f (R.x k)‖ * ‖stepOf P Δ c‖ := by sorry

end LewisTorczon.BoundPS
