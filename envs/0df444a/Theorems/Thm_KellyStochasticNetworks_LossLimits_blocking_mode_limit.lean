-- Prove2me | Theorems.Thm_KellyStochasticNetworks_LossLimits_blocking_mode_limit
-- name    : KellyStochasticNetworks.LossLimits.blocking_mode_limit
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:47:06.322195+00:00
-- url     : https://prove2.me/theorems/80bafa6c-d05d-4053-bc3e-7a3563234a0a
-- title:
--   Lemma 3.13 — convergence of blocking vectors and continuous modes
-- statement:
--   Fix a natural matrix $A\in\mathbb N^{J\times R}$ of full row rank. For $N\ge1$, let $\nu_r(N)>0$ and let $C_j(N)$ be positive integers, with $\nu_r(N)/N\to\nu_r>0$ and $C_j(N)/N\to C_j>0$. Let $B(N)$ and $B$ solve the corresponding blocking conditions (3.6), and set $x_r(N)=\nu_r(N)\prod_j(1-B_j(N))^{A_{jr}}$ and $x_r=\nu_r\prod_j(1-B_j)^{A_{jr}}$. Assume strict slack $(Ax)_j<C_j$ at every link with $B_j=0$.
--
--   Then the finite-dimensional vectors satisfy
--   $$B(N)\longrightarrow B,\qquad \frac{x(N)}N\longrightarrow x.$$
--
--   This identifies the blocking constraints and variances that enter the Gaussian limit.
--
--   **Formalization Note** The strict-slack condition stated before the source lemma is retained, although its proof does not use it (F2). The blocking vector is selected from the actual equations rather than supplied with a convergence hypothesis; the real-capacity companion provides its characterization at the limit.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 62 (PDF p. 70), Lemma 3.13, proof printed pp. 62–63 / PDF pp. 70–71; DOI 10.1017/cbo9781139565363.

import Mathlib
import Definitions.Def_KellyStochasticNetworks_LossLimits_Optimization

open Filter Topology

namespace KellyStochasticNetworks.LossLimits

/-- Lemma 3.13. `Scaling` means full row rank of the fixed natural matrix,
positive rates and natural capacities for N≥1, positive real limiting data,
and coordinatewise ν(N)/N→ν, C(N)/N→C. `blocking` selects the solution of (3.6):
0≤B<1, load≤capacity, equality on B>0. `mode` is ν_r∏_j(1-B_j)^A_jr.
`strictSlack` requires load_j<C_j whenever the selected limiting B_j=0. -/
theorem blocking_mode_limit {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (νN : ℕ → Fin R → ℝ) (CN : ℕ → Fin J → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℝ)
    (hscale : Scaling A νN CN ν C) (hslack : strictSlack A ν C) :
    Tendsto (fun N => blocking A (νN N) (fun j => (CN N j : ℝ)))
      atTop (𝓝 (blocking A ν C)) ∧
    Tendsto (fun N => fun r => mode A (νN N) (fun j => (CN N j : ℝ)) r / N)
      atTop (𝓝 (mode A ν C)) := by sorry

end KellyStochasticNetworks.LossLimits
