-- Prove2me | Theorems.Thm_IdentifiableVAE_identifiability_up_to_linear
-- name    : IdentifiableVAE.identifiability_up_to_linear
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:58:47.769007+00:00
-- url     : https://prove2.me/theorems/9209ddf5-14c8-49ca-8efb-27ee2090a620
-- title:
--   Theorem 1 (as proved): identifiability up to $\sim_A$
-- statement:
--   Let $k\ge1$, $n\le d$, and let $U\subset\mathbb{R}^m$ be open. Let the noise law $P_\varepsilon$ be a probability measure on $\mathbb{R}^d$ with a density. Let $\theta=(f,Q,T,\lambda)$ describe a model (5)-(7) on $U$: $f$ is measurable and injective, which is assumption (ii), $Q_i>0$, and the factors are normalisable. Assume:
--
--   1. (i) the zero set $\{\omega\in\mathbb{R}^d:\varphi_\varepsilon(\omega)=0\}$ of the noise characteristic function is Lebesgue-null;
--   2. (iii) each $T_{i,j}$ is differentiable almost everywhere, and for each $i$ no nonzero $\alpha\in\mathbb{R}^k$ makes $\sum_j\alpha_jT_{i,j}$ constant on a set of positive measure;
--   3. (iv) there are $nk+1$ distinct points $u^0,\dots,u^{nk}\in U$ such that the $nk\times nk$ matrix
--   $$L=\big(\lambda(u^1)-\lambda(u^0),\dots,\lambda(u^{nk})-\lambda(u^0)\big)$$
--   is invertible.
--
--   Then $\theta$ is $\sim_A$-identifiable. Let $\tilde\theta$ be any parameter describing a model on $U$ with $p_{\tilde\theta}(x\mid u)=p_\theta(x\mid u)$ for all $u\in U$. Then there are an invertible $nk\times nk$ matrix $A$ and $c\in\mathbb{R}^{nk}$ such that, for Lebesgue-almost every $z\in\mathbb{R}^n$, $f(z)$ lies in the image of $\tilde f$ and
--
--   $$\mathbf T(z)=A\,\tilde{\mathbf T}\big(\tilde f^{-1}(f(z))\big)+c.$$
--
--   This is the paper's main result: the latents are recovered up to the pointwise maps $\mathbf T,\tilde{\mathbf T}$ and one invertible linear map.
--
--   **Formalization Note** The statement differs from the printed theorem in three places.
--   1. The paper's conclusion holds for every $x$ in the image of $f$. A parameter can be changed on a null set without changing any observed law, so only the almost-everywhere version holds, and that is what the proof gives.
--   2. Assumption (iii) is printed with linear independence on subsets of $\mathcal X$. It is read as linear independence together with the constants, on subsets of $\mathbb{R}$. The literal reading admits $T\equiv1$, for which the theorem fails.
--   3. Assumption (i) is printed for subsets of $\mathcal X$. It is stated for frequencies $\omega\in\mathbb{R}^d$, which is where the proof uses it.
-- source:
--   Khemakhem, Kingma, Monti and Hyvärinen, Variational Autoencoders and Nonlinear ICA: A Unifying Framework, AISTATS 2020, arXiv:1907.04809v4, Section 4.1, Theorem 1, eqs. (5)-(7), (13), (14), p. 5; proof in Appendix B.2, eqs. (20)-(32), pp. 13-14

import Mathlib
import Definitions.Def_IdentifiableVAE_Basic

open MeasureTheory

namespace IdentifiableVAE

theorem identifiability_up_to_linear {n d m k : ℕ} (hk : 1 ≤ k) (hnd : n ≤ d)
    (U : Set (Fin m → ℝ)) (hU : IsOpen U)
    (Pε : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure Pε] (hPε : Pε ≪ volume)
    (θ : Param n d m k) (hθ : IsParam θ U)
    (h1 : CharFunZeroNull Pε) (h3 : SuffStatRegular θ) (h4 : HasInvertibleL θ U) :
    IdentifiableUpTo Pε U {θ' | IsParam θ' U} SimAAE θ := by sorry

end IdentifiableVAE
