-- Prove2me | Theorems.Thm_GoodViewsNotEnough_iid_ep_expectation
-- name    : GoodViewsNotEnough.iid_ep_expectation
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T18:49:24.504506+00:00
-- url     : https://prove2.me/theorems/50e7d582-135e-427b-b41d-903b26bc5f63
-- title:
--   Eq. (7): exact expectation of the i.i.d. Epps–Pulley statistic
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb{R}$, let $\nu$ be a finite frequency measure on $\mathbb{R}$, and let $N\ge1$. If $y_1,\dots,y_N$ are i.i.d. with law $\mu$ and $\hat\mu_N=\frac1N\sum_n\delta_{y_n}$, then the Epps–Pulley statistic $N\,D_\nu(\hat\mu_N)$ has expectation
--
--   $$R_{N,\nu}(\mu)=\mathbb{E}\big[N\,D_\nu(\hat\mu_N)\big]=N\,D_\nu(\mu)+A_\nu-J_\nu(\mu),$$
--
--   where $D_\nu(\mu)=\int|\varphi_\mu-g|^2d\nu$, $A_\nu=\nu(\mathbb{R})$ and $J_\nu(\mu)=\int|\varphi_\mu|^2d\nu$.
--
--   This identity converts every expected Epps–Pulley objective of the scalar model into a deterministic function of the output law.
--
--   **Formalization Note** The conditions $N\ge1$ and $\nu(\mathbb{R})<\infty$ are implicit in the paper: the formula fails for $N=0$, and $A_\nu$ must be a real number.
-- source:
--   Anran Xu, Good Views Are Not Enough: Global Counterexamples for Gaussian-Regularized JEPAs, arXiv:2611.12137v1 (2026), Appendix A, eqs. (6)-(7), p. 11

import Mathlib
import Definitions.Def_GoodViewsNotEnough_Basic

open MeasureTheory Complex

namespace GoodViewsNotEnough

theorem iid_ep_expectation (N : ℕ) (hN : 0 < N) (ν μ : Measure ℝ) [IsFiniteMeasure ν]
    [IsProbabilityMeasure μ] :
    iidEP N ν μ = N * discrepancy ν μ + freqMass ν - selfTerm ν μ := by sorry

end GoodViewsNotEnough
