-- Prove2me | Theorems.Thm_NeuralCollapseCE_minimizers_equidistribute
-- name    : NeuralCollapseCE.minimizers_equidistribute
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:12:40.897091+00:00
-- url     : https://prove2.me/theorems/c345cd66-3bf7-4086-ae56-8e12cb611502
-- title:
--   Theorem 3: minimising configurations equidistribute on the sphere
-- statement:
--   Let $d\ge1$ and $\alpha>0$. For every $n$ let $u^{(n)}=(u^{(n)}_1,\dots,u^{(n)}_n)$ be a global minimiser of $\mathcal{L}_\alpha$ over unit vectors of $\mathbb{R}^d$, and let
--
--   $$\mu_n=\frac1n\sum_{i=1}^n\delta_{u^{(n)}_i}$$
--
--   be the probability measure it generates on $\mathbb{S}^d$. Then $\mu_n$ converges weakly to the uniform probability measure $\sigma_d$ as $n\to\infty$: for every continuous $f:\mathbb{S}^d\to\mathbb{R}$,
--
--   $$\frac1n\sum_{i=1}^nf\big(u^{(n)}_i\big)\longrightarrow\int_{\mathbb{S}^d}f\,d\sigma_d.$$
--
--   In words, when there are many more points than dimensions the minimisers of the contrastive-type loss spread out uniformly.
--
--   **Formalization Note** Weak convergence is written as convergence of integrals of all continuous real functions, which on the compact sphere are bounded. The statement holds for every choice of minimisers, one for each $n$.
-- source:
--   Lu and Steinerberger, Neural collapse with cross-entropy loss, arXiv:2012.08465v2 (2021), Section 1.3, Theorem 3, p. 3; proof in Section 4, pp. 9-10

import Mathlib
import Definitions.Def_NeuralCollapseCE_Basic

open MeasureTheory Filter Topology Asymptotics

namespace NeuralCollapseCE

theorem minimizers_equidistribute {d : ℕ} (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (u : (n : ℕ) → Fin n → Sph d)
    (hu : ∀ n, IsSymMinimizer α (fun i => ((u n i : Sph d) : Vec d))) :
    ∀ f : C(Sph d, ℝ),
      Tendsto (fun n => ∫ x, f x ∂(empiricalMeasure (u n))) atTop
        (𝓝 (∫ x, f x ∂(uniformSphere d))) := by sorry

end NeuralCollapseCE
