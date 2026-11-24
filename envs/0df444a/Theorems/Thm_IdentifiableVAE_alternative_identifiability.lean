-- Prove2me | Theorems.Thm_IdentifiableVAE_alternative_identifiability
-- name    : IdentifiableVAE.alternative_identifiability
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:01:36.997179+00:00
-- url     : https://prove2.me/theorems/a6486afa-192a-4677-be37-bfdfec7e7ac1
-- title:
--   Theorem 6 (first claim, as proved): identifiability up to $\sim$ from an invertible Jacobian of $\lambda$
-- statement:
--   Let $k\ge1$, $n\le d$, let $U\subset\mathbb{R}^m$ be open, and let the noise law have a density whose characteristic function vanishes only on a Lebesgue-null set (assumption (i)). Let $\theta$ describe a model on $U$; in particular $f$ is injective (assumption (ii)). Assume:
--
--   1. (iii) each $T_{i,j}$ is differentiable almost everywhere with $T_{i,j}'\ne0$ almost everywhere;
--   2. (iv) $\lambda$ is differentiable on $U$, and there is $u_0\in U$ at which the Jacobian $J_\lambda(u_0)$ is invertible. In particular $m=nk$.
--
--   Let $\tilde\theta$ be a parameter describing a model on $U$ whose $\tilde\lambda$ is differentiable on $U$, with $p_{\tilde\theta}(x\mid u)=p_\theta(x\mid u)$ for all $u\in U$. Then $\theta\sim\tilde\theta$: there are a matrix $A$ and $c\in\mathbb{R}^{nk}$ such that, for almost every $z$, $f(z)=\tilde f(\tilde z)$ for some $\tilde z$ and
--
--   $$\mathbf T(z)=A\,\tilde{\mathbf T}(\tilde z)+c.$$
--
--   **Formalization Note** The statement leaves out three things.
--   1. The theorem's second claim is not included: that $\tilde T$ and $\tilde\lambda$ again satisfy (iii) and (iv). It is false. Take $n=1$, $k=2$, $T=(t,t)$, $\lambda(u)=u$, and $\tilde T=(t,t^2)$, $\tilde\lambda(u)=(u_1+u_2,0)$ with the same Gaussian base measure. These give the same model, and $J_{\tilde\lambda}$ is singular everywhere.
--   2. The relation is the paper's $\sim$ with an arbitrary matrix $A$. In the example above no invertible $A$ exists.
--   3. The differentiability of $\tilde\lambda$, which the proof assumes explicitly, is part of the competing class. As elsewhere, the conclusion is stated almost everywhere.
-- source:
--   Khemakhem, Kingma, Monti and Hyvärinen, Variational Autoencoders and Nonlinear ICA: A Unifying Framework, AISTATS 2020, arXiv:1907.04809v4, Appendix E, Theorem 6, p. 19; proof eqs. (58)-(60), p. 20

import Mathlib
import Definitions.Def_IdentifiableVAE_Basic

open MeasureTheory

namespace IdentifiableVAE

theorem alternative_identifiability {n d m k : ℕ} (hk : 1 ≤ k) (hnd : n ≤ d)
    (U : Set (Fin m → ℝ)) (hU : IsOpen U)
    (Pε : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure Pε] (hPε : Pε ≪ volume)
    (θ : Param n d m k) (hθ : IsParam θ U) (h1 : CharFunZeroNull Pε)
    (h3 : ∀ i j, (∀ᵐ t ∂(volume : Measure ℝ), DifferentiableAt ℝ (θ.T i j) t) ∧
      ∀ᵐ t ∂(volume : Measure ℝ), deriv (θ.T i j) t ≠ 0)
    (h4 : DifferentiableOn ℝ θ.lam U ∧ ∃ u₀ ∈ U, (fderiv ℝ θ.lam u₀).IsInvertible) :
    IdentifiableUpTo Pε U {θ' | IsParam θ' U ∧ DifferentiableOn ℝ θ'.lam U} SimAE θ := by sorry

end IdentifiableVAE
