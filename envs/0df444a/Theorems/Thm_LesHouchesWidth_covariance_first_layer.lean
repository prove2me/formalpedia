-- Prove2me | Theorems.Thm_LesHouchesWidth_covariance_first_layer
-- name    : LesHouchesWidth.covariance_first_layer
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:01:19.149896+00:00
-- url     : https://prove2.me/theorems/2f6320be-74d6-427f-9844-9134c9fb5b18
-- title:
--   Eq. (10): first-layer covariance $\mathbb E[z^{(1)}_i(x)z^{(1)}_i(x')]=K^{(1)}(x,x')$
-- statement:
--   For a network with Gaussian initialization $b^{(1)}_i\sim\mathcal N(0,\sigma_b^2)$ and $W^{(1)}_{ij}\sim\mathcal N(0,\sigma_w^2/n_0)$, any inputs $x,x'\in\mathbb R^{n_0}$ and any first-layer neuron $i$,
--   $$\mathbb E\big[z^{(1)}_i(x)\,z^{(1)}_i(x')\big]=\sigma_b^2+\sigma_w^2\,\frac{x\cdot x'}{n_0}=K^{(1)}(x,x').$$
--
--   This is the base case of the NNGP kernel recursion.
--
--   **Formalization Note** In Lecture 1 this quantity is written $\mathbb E[z^0_i(x)z^0_i(x')]=K^0(x,x')$; the series uses the layer indexing of Lectures 4–5.
-- source:
--   Bahri, Hanin, Brossollet, Erba, Keup, Pacelli, Simon, *Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3 (https://arxiv.org/abs/2309.01592), p. 4, eq. (10) (Lecture 1, Section 1.3, proof of Result 1).

import Mathlib
import Definitions.Def_LesHouchesWidth_GaussianMLP

namespace LesHouchesWidth

open MeasureTheory ProbabilityTheory

theorem covariance_first_layer (σb σw : ℝ) (φ : ℝ → ℝ) (n : ℕ → ℕ) (L : ℕ)
    (x x' : Fin (n 0) → ℝ) (i : Fin (n 1)) :
    ∫ θ, mlpZ (σb ^ 2) (σw ^ 2) φ θ x 1 i * mlpZ (σb ^ 2) (σw ^ 2) φ θ x' 1 i
        ∂(stdGaussianParams n L) =
      nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x x' := by sorry

end LesHouchesWidth
