-- Prove2me | Theorems.Thm_LesHouchesWidth_nngp_limit_deep
-- name    : LesHouchesWidth.nngp_limit_deep
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-23T22:27:26.076685+00:00
-- url     : https://prove2.me/theorems/b7447bd9-7f68-4bde-a589-b364da910fd1
-- title:
--   Eqs. (13)–(14): deep networks converge to the NNGP (simultaneous infinite-width limit)
-- statement:
--   Let $\varphi$ be continuous with a linear envelope, $|\varphi(u)|\le c+M|u|$. Fix a depth $L$, input width $n_0$, output width $n_{\mathrm{out}}$ and inputs $x_1,\dots,x_m\in\mathbb R^{n_0}$. Consider the network with all hidden widths equal to $N$ and Gaussian initialization ($\sigma_b^2$, $\sigma_w^2/n_{\ell-1}$). As $N\to\infty$ the vector $(z^{(L+1)}_i(x_a))_{i\le n_{\mathrm{out}},\,a\le m}$ converges in distribution to the centered Gaussian with covariance
--   $$\mathrm{Cov}\big(z^{(L+1)}_i(x_a),z^{(L+1)}_j(x_b)\big)=\delta_{ij}\,K^{(L+1)}(x_a,x_b),$$
--   where $K^{(\ell)}$ is the NNGP kernel recursion (13)–(14). That is, for every bounded continuous $g$, $\mathbb E\,g(z^{(L+1)})\to\int g\,d\mathcal N(0,\delta_{ij}K^{(L+1)})$.
--
--   This extends Result 1 to finite depth in the simultaneous limit.
--
--   **Formalization Note** The notes do not state conditions on $\varphi$. The continuity and linear-envelope condition is taken from Matthews et al. (2018).
-- source:
--   Bahri, Hanin, Brossollet, Erba, Keup, Pacelli, Simon, *Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3 (https://arxiv.org/abs/2309.01592), p. 5, Section 1.4, eqs. (13)–(14) (simultaneous limit; the notes refer to refs. [2,3] for proofs).

import Mathlib
import Definitions.Def_LesHouchesWidth_GaussianMLP

namespace LesHouchesWidth

open MeasureTheory ProbabilityTheory

theorem nngp_limit_deep (σb σw : ℝ) (φ : ℝ → ℝ) (hφ : Continuous φ)
    (hφ_env : ∃ c M : ℝ, ∀ u, |φ u| ≤ c + M * |u|)
    (L n0 nOut m : ℕ) (xs : Fin m → Fin n0 → ℝ)
    (g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin nOut × Fin m)) ℝ) :
    Filter.Tendsto
      (fun N : ℕ => ∫ θ, g (outputVector (σb ^ 2) (σw ^ 2) φ
          (uniformWidths_last n0 nOut L N) xs θ)
        ∂(stdGaussianParams (uniformWidths n0 nOut L N) L))
      Filter.atTop
      (nhds (∫ v, g v ∂(multivariateGaussian 0
        (blockDiagCov (k := nOut) fun a b => nngpKernel (σb ^ 2) (σw ^ 2) φ (L + 1) (xs a) (xs b))))) := by sorry

end LesHouchesWidth
