-- Prove2me | Theorems.Thm_LesHouchesWidth_nngp_limit_one_hidden_layer
-- name    : LesHouchesWidth.nngp_limit_one_hidden_layer
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:29:45.771985+00:00
-- url     : https://prove2.me/theorems/c38c8303-b585-4735-9711-8bed11db8f8b
-- title:
--   Result 1: a one-hidden-layer network converges to a Gaussian process as $n\to\infty$
-- statement:
--   Consider a fully connected network with one hidden layer of width $n$, input width $n_0$ and output width $n_2$, with independent parameters
--   $$b^{(1)}_i\sim\mathcal N(0,\sigma_b^2),\quad W^{(1)}_{ij}\sim\mathcal N\Big(0,\frac{\sigma_w^2}{n_0}\Big),\quad b^{(2)}_i\sim\mathcal N(0,\sigma_b^2),\quad W^{(2)}_{ij}\sim\mathcal N\Big(0,\frac{\sigma_w^2}{n}\Big),$$
--   and a measurable nonlinearity $\varphi$. Fix inputs $x_1,\dots,x_m$ such that $\varphi^2$ is integrable against $\mathcal N(0,K^{(1)}(x_a,x_a))$ for each $a$. Then, as $n\to\infty$, the vector $(z^{(2)}_i(x_a))_{i\le n_2,\,a\le m}$ converges in distribution to a centered Gaussian vector with covariance
--   $$\delta_{ij}\,K^{(2)}(x_a,x_b),\qquad K^{(2)}(x,x')=\sigma_b^2+\sigma_w^2\,\mathbb E_{(u_1,u_2)\sim\mathcal N(0,\Sigma)}[\varphi(u_1)\varphi(u_2)],$$
--   with $\Sigma$ the $2\times2$ matrix of $K^{(1)}(x,x')=\sigma_b^2+\sigma_w^2x\cdot x'/n_0$ values. In particular the output is a Gaussian process with mean $0$ and kernel $K^{(2)}$, and distinct outputs are independent.
--
--   This is Neal's observation that wide single-hidden-layer networks define Gaussian process priors over functions.
--
--   **Formalization Note** Convergence in distribution is expressed with bounded continuous test functions. Lecture 1 writes $z^1$ and $K^1$ for what is $z^{(2)}$ and $K^{(2)}$ here.
-- source:
--   Bahri, Hanin, Brossollet, Erba, Keup, Pacelli, Simon, *Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3 (https://arxiv.org/abs/2309.01592), p. 3, Result 1, eqs. (5)–(7) (Lecture 1, Section 1.3).

import Mathlib
import Definitions.Def_LesHouchesWidth_GaussianMLP

namespace LesHouchesWidth

open MeasureTheory ProbabilityTheory

theorem nngp_limit_one_hidden_layer (σb σw : ℝ) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (n0 n2 m : ℕ) (xs : Fin m → Fin n0 → ℝ)
    (hφ2 : ∀ a, Integrable (fun u => φ u ^ 2)
      (gaussianReal 0 (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (xs a) (xs a)).toNNReal))
    (g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin n2 × Fin m)) ℝ) :
    Filter.Tendsto
      (fun N : ℕ => ∫ θ, g (outputVector (σb ^ 2) (σw ^ 2) φ
          (uniformWidths_last n0 n2 1 N) xs θ)
        ∂(stdGaussianParams (uniformWidths n0 n2 1 N) 1))
      Filter.atTop
      (nhds (∫ v, g v ∂(multivariateGaussian 0
        (blockDiagCov (k := n2) fun a b => nngpKernel (σb ^ 2) (σw ^ 2) φ 2 (xs a) (xs b))))) := by sorry

end LesHouchesWidth
