-- Prove2me | Theorems.Thm_LesHouchesWidth_jacobian_second_moment
-- name    : LesHouchesWidth.jacobian_second_moment
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:23:45.263113+00:00
-- url     : https://prove2.me/theorems/cd91d20d-dc2a-4630-8ff3-9da2c479c0d2
-- title:
--   Eq. (124): $\mathbb E[(\partial z^{(L+1)}_q/\partial x_p)^2]=2/n_0$ for random ReLU networks
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R$ that has a density with respect to Lebesgue measure, is symmetric about $0$, and has variance $1$. Let $L\ge1$ and $n_0,\dots,n_{L+1}\ge1$, and consider the ReLU network with weights $W^{(\ell)}_{ij}=(2/n_{\ell-1})^{1/2}\widehat W^{(\ell)}_{ij}$, $\widehat W^{(\ell)}_{ij}$ i.i.d. $\sim\mu$, and zero biases. Then for every fixed input $x\neq0$ and all $p\le n_0$, $q\le n_{L+1}$,
--   $$\mathbb E\Big[\Big(\frac{\partial z^{(L+1)}_q}{\partial x_p}(x)\Big)^2\Big]=\frac{2}{n_0}.$$
--
--   The second moment of the input–output Jacobian is independent of depth and of the hidden widths. This is the exact sense in which $C_W=2$ is the critical initialization for ReLU networks.
--
--   **Formalization Note** The Jacobian entry is the Fréchet derivative, taken to be $0$ where the network is not differentiable. Since $2/n_0\neq0$, the equation also asserts integrability.
-- source:
--   Bahri, Hanin, Brossollet, Erba, Keup, Pacelli, Simon, *Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3 (https://arxiv.org/abs/2309.01592), p. 41, eq. (124) (Section 5.5.1), under the assumptions of Section 5.3 (p. 39).

import Mathlib
import Definitions.Def_LesHouchesWidth_ReLUNet

namespace LesHouchesWidth

open MeasureTheory ProbabilityTheory

theorem jacobian_second_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ_ac : μ ≪ volume) (hμ_symm : μ.map (fun t : ℝ => -t) = μ)
    (hμ_var : ∫ t, t ^ 2 ∂μ = 1)
    (L : ℕ) (hL : 1 ≤ L) (n : ℕ → ℕ) (hn : ∀ ℓ ≤ L + 1, 1 ≤ n ℓ)
    (x : Fin (n 0) → ℝ) (hx : x ≠ 0) (p : Fin (n 0)) (q : Fin (n (L + 1))) :
    ∫ ω, (jacobianEntry ω x p q) ^ 2 ∂(weightLaw n L μ) = 2 / (n 0 : ℝ) := by sorry

end LesHouchesWidth
