-- Prove2me | Theorems.Thm_Katyusha_NonSC_lemma_2_7
-- name    : Katyusha.NonSC.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:34:54.559068+00:00
-- url     : https://prove2.me/theorems/75d06781-1513-4cb9-85e0-6e55018d190b
-- title:
--   Lemma 2.7 ($\sigma=0$) — one-iteration coupling inequality
-- statement:
--   Consider Problem (1.1): $F(x)=f(x)+\psi(x)$ with $f=\frac1n\sum_{i=1}^n f_i$ on $\mathbb R^d$, $n\ge1$, where each $f_i$ is convex and $L$-smooth ($\|\nabla f_i(x)-\nabla f_i(y)\|\le L\|x-y\|$, $L>0$) and $\psi$ is convex. Let $x^*$ be a minimizer of $F$.
--
--   Fix $\alpha>0$ and $\tau_1$ with $0<\tau_1\le\frac12$ and $\tau_1\le\frac{1}{3\alpha L}$, and let $\tau_2=\frac12$. Fix points $y_k,z_k,\widetilde x\in\mathbb R^d$ and set $x_{k+1}=\tau_1 z_k+\tau_2\widetilde x+(1-\tau_1-\tau_2)y_k$. For an index $i$ drawn uniformly from $\{1,\dots,n\}$ let $\widetilde\nabla_{k+1}=\nabla f(\widetilde x)+\nabla f_i(x_{k+1})-\nabla f_i(\widetilde x)$,
--   $$y_{k+1}=\arg\min_y\Big\{\tfrac{3L}{2}\|y-x_{k+1}\|^2+\langle\widetilde\nabla_{k+1},y\rangle+\psi(y)\Big\},\qquad z_{k+1}=\arg\min_z\Big\{\tfrac1{2\alpha}\|z-z_k\|^2+\langle\widetilde\nabla_{k+1},z\rangle+\psi(z)\Big\}.$$
--   Then, with $\mathbb E$ the expectation over $i$,
--   $$0\le\frac{\alpha(1-\tau_1-\tau_2)}{\tau_1}\big(F(y_k)-F(x^*)\big)-\frac{\alpha}{\tau_1}\big(\mathbb E[F(y_{k+1})]-F(x^*)\big)+\frac{\alpha\tau_2}{\tau_1}\big(F(\widetilde x)-F(x^*)\big)+\frac12\|z_k-x^*\|^2-\frac12\mathbb E\big[\|z_{k+1}-x^*\|^2\big].$$
--
--   This is the one-iteration inequality of Katyusha, combining the proximal gradient step, the variance bound and the mirror step; summed over an epoch it gives inequality (C.1), the starting point of the analysis of $\mathtt{Katyusha}^{\mathrm{ns}}$.
--
--   **Formalization Note** This is Lemma 2.7 for $\sigma=0$, the case used by Theorem 4.1 ($\psi$ convex, not necessarily strongly convex), so the coefficient of the last term is $\frac{1+\alpha\sigma}{2}=\frac12$. The hypotheses $\alpha>0$ and $0<\tau_1\le\frac12$ are implicit in the paper (it divides by $\tau_1$, and $x_{k+1}$ must be a convex combination; $\tau_1=\min\{\cdot,\frac12\}$ in Algorithm 1 and $\tau_{1,s}=\frac2{s+4}\le\frac12$ in Algorithm 2). The two arg-min points are produced by a map $P$ assumed to return proximal points of $\psi$ for every positive step; the gradients $\nabla f_i$ are tied to $f_i$ by `HasGradientAt`. $\psi$ is real-valued (extended-valued $\psi$ such as indicator functions are not covered).
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, p. 11, Lemma 2.7 (with the choices of Lemma 2.6, p. 10), case σ = 0 as used in App. C.1, p. 26

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_IsProxPoint
import Definitions.Def_Katyusha_NonSC_step

namespace Katyusha.NonSC

/-- Lemma 2.7 (coupling step 2) of Allen-Zhu, arXiv:1603.05953v6, p. 11, in the non-strongly convex
case `σ = 0`, under the choices of Lemma 2.6 (p. 10): `x_{k+1} = τ₁ z_k + τ₂ x̃ + (1 - τ₁ - τ₂) y_k`
with `τ₁ ≤ 1/(3αL)` and `τ₂ = 1/2`. The expectation is over the index `i`, uniform on `Fin n`;
`(y_{k+1}, z_{k+1}) = innerStep … (y_k, z_k) i`. -/
theorem lemma_2_7 {d n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ) (hL : 0 < L)
    (hf_grad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hf_conv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hf_smooth : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hψ : ConvexOn ℝ Set.univ ψ)
    (P : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ γ : ℝ, 0 < γ → ∀ v, SAGA.Convex.IsProxPoint ψ γ v (P γ v))
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ x, obj f ψ xstar ≤ obj f ψ x)
    (τ1 α : ℝ) (hα : 0 < α) (hτ1 : 0 < τ1) (hτ1_half : τ1 ≤ 1 / 2)
    (hτ1α : τ1 ≤ 1 / (3 * α * L))
    (xt y z : EuclideanSpace ℝ (Fin d)) :
    0 ≤ α * (1 - τ1 - tau2) / τ1 * (obj f ψ y - obj f ψ xstar)
        - α / τ1 * ((1 / (n : ℝ)) * (∑ i, obj f ψ (innerStep f' P L τ1 α xt (y, z) i).1)
            - obj f ψ xstar)
        + α * tau2 / τ1 * (obj f ψ xt - obj f ψ xstar)
        + 1 / 2 * ‖z - xstar‖ ^ 2
        - 1 / 2 * ((1 / (n : ℝ)) * ∑ i, ‖(innerStep f' P L τ1 α xt (y, z) i).2 - xstar‖ ^ 2) := by sorry

end Katyusha.NonSC
