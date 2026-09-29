-- Prove2me | Theorems.Thm_LesHouchesWidth_covariance_second_layer
-- name    : LesHouchesWidth.covariance_second_layer
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:02:30.32487+00:00
-- url     : https://prove2.me/theorems/83b1415a-dd75-4855-bcf3-3ab332189bc6
-- title:
--   Eqs. (9), (11): second-layer covariance $\mathbb E[z^{(2)}_i(x)z^{(2)}_i(x')]=K^{(2)}(x,x')$ at finite width
-- statement:
--   Let $\varphi$ be measurable with $\varphi^2$ integrable against $\mathcal N(0,K^{(1)}(x,x))$ and against $\mathcal N(0,K^{(1)}(x',x'))$. For a network of depth $L\ge1$ with first hidden layer of width $n_1\ge1$ and Gaussian initialization ($\sigma_b^2$, $\sigma_w^2/n_{\ell-1}$), and any second-layer neuron $i$,
--   $$\mathbb E\big[z^{(2)}_i(x)\,z^{(2)}_i(x')\big]=\sigma_b^2+\sigma_w^2\,\mathbb E_{(u_1,u_2)\sim\mathcal N(0,\Sigma)}\big[\varphi(u_1)\varphi(u_2)\big]=K^{(2)}(x,x'),\qquad \Sigma=\begin{pmatrix}K^{(1)}(x,x)&K^{(1)}(x,x')\\K^{(1)}(x',x)&K^{(1)}(x',x')\end{pmatrix}.$$
--
--   The identity holds exactly at every finite width $n_1$. It is the computation behind the kernel in Result 1.
--
--   **Formalization Note** In Lecture 1 notation this is $\mathbb E[z^1_i(x)z^1_i(x')]=K^1(x,x')$.
-- source:
--   Bahri, Hanin, Brossollet, Erba, Keup, Pacelli, Simon, *Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3 (https://arxiv.org/abs/2309.01592), p. 4, eqs. (9) and (11)–(12) (Lecture 1, Section 1.3, proof of Result 1).

import Mathlib
import Definitions.Def_LesHouchesWidth_GaussianMLP

namespace LesHouchesWidth

open MeasureTheory ProbabilityTheory

theorem covariance_second_layer (σb σw : ℝ) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (n : ℕ → ℕ) (L : ℕ) (hL : 1 ≤ L) (hn : 1 ≤ n 1)
    (x x' : Fin (n 0) → ℝ)
    (hφx : Integrable (fun u => φ u ^ 2)
      (gaussianReal 0 (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x x).toNNReal))
    (hφx' : Integrable (fun u => φ u ^ 2)
      (gaussianReal 0 (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x' x').toNNReal))
    (i : Fin (n 2)) :
    ∫ θ, mlpZ (σb ^ 2) (σw ^ 2) φ θ x 2 i * mlpZ (σb ^ 2) (σw ^ 2) φ θ x' 2 i
        ∂(stdGaussianParams n L) =
      nngpKernel (σb ^ 2) (σw ^ 2) φ 2 x x' := by sorry

end LesHouchesWidth
