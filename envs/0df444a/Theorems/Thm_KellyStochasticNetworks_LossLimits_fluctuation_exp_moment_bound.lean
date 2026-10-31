-- Prove2me | Theorems.Thm_KellyStochasticNetworks_LossLimits_fluctuation_exp_moment_bound
-- name    : KellyStochasticNetworks.LossLimits.fluctuation_exp_moment_bound
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-31T05:11:13.563361+00:00
-- url     : https://prove2.me/theorems/9af8c28e-12b9-4df1-bc6d-17f4aa2a6134
-- title:
--   Theorem 3.14 (tail control) — uniform exponential moments of $u(N)$
-- statement:
--   **Setting (limiting regime of §3.5.1).** Fix a matrix $A\in\mathbb N^{J\times R}$ of full row rank. For $N\ge 1$ let $\nu_r(N)>0$ and let $C_j(N)$ be positive integers with $\nu_r(N)/N\to\nu_r>0$ and $C_j(N)/N\to C_j>0$. Let $B$ be the solution of the blocking conditions (3.6) for the limiting data $(\nu,C)$, put $x_r=\nu_r\prod_j(1-B_j)^{A_{jr}}$, and assume strict slack: $(Ax)_j<C_j$ whenever $B_j=0$. Let $x(N)$ be the corresponding mode for the data $(\nu(N),C(N))$.
--
--   Let $n(N)$ have the exact stationary law (3.3), proportional to $\prod_r \nu_r(N)^{n_r}/n_r!$ on $\{n\in\mathbb N^R: An\le C(N)\}$, and let $u(N)=(n(N)-x(N))/\sqrt N$.
--
--   **Claim (uniform exponential moments).** For every fixed $\eta\in\mathbb R^R$:
--
--   1. $\mathbb E\,e^{\eta\cdot u(N)}<\infty$ for every $N\ge1$;
--   2. there is a constant $M$ (depending on $\eta$) such that $$\mathbb E\,e^{\eta\cdot u(N)}\le M$$ for all sufficiently large $N$.
--
--   This is the tail control required in Remark 3.16 ("we also need to ensure that the probability mass outside of a compact set decays quickly enough that moments can be calculated from the limit distribution"); it yields tightness of $u(N)$ and uniform integrability of every polynomial moment.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF (statslab.cam.ac.uk/~frank/STOCHNET/LNSN/book.pdf), §3.5.2, printed pp. 64–66 (PDF pp. 72–74): Theorem 3.14 and Remark 3.16 (tightness/tail control of u(N)); DOI 10.1017/cbo9781139565363.

import Mathlib
import Definitions.Def_KellyStochasticNetworks_LossLimits_Laws

open MeasureTheory Filter Topology

namespace KellyStochasticNetworks.LossLimits

/-- Uniform exponential moments of the centred, scaled occupancy vector
u(N) = (n(N) - x(N))/sqrt N in the limiting regime of §3.5.1 (the tail control of
Remark 3.16 underlying Theorem 3.14). For every fixed real vector η, the variable
exp(η·u(N)) is integrable under the exact fluctuation law for every N ≥ 1, and its
mean is bounded uniformly for all large N. -/
theorem fluctuation_exp_moment_bound {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (νN : ℕ → Fin R → ℝ) (CN : ℕ → Fin J → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℝ)
    (hscale : Scaling A νN CN ν C) (hslack : strictSlack A ν C) (η : Fin R → ℝ) :
    (∀ N, 0 < N → Integrable (fun u : Fin R → ℝ => Real.exp (∑ r, η r * u r))
      (fluctuationLaw A νN CN N)) ∧
    ∃ M : ℝ, ∀ᶠ N in atTop,
      ∫ u, Real.exp (∑ r, η r * u r) ∂(fluctuationLaw A νN CN N) ≤ M := by sorry

end KellyStochasticNetworks.LossLimits
