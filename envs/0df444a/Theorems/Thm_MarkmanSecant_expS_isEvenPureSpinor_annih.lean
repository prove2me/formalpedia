-- Prove2me | Theorems.Thm_MarkmanSecant_expS_isEvenPureSpinor_annih
-- name    : MarkmanSecant.expS_isEvenPureSpinor_annih
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T14:59:55.136305+00:00
-- url     : https://prove2.me/theorems/e77dfab1-35c7-4bc2-aaf1-5af629005d45
-- title:
--   Equation (2.4.6): $\exp(c\Theta)$ is an even pure spinor with annihilator $\{(-c\,\theta(t),t)\}$
-- statement:
--   **Equation (2.4.6) of Markman, arXiv:2502.03415.**
--
--   Let $X$ be a complex torus of dimension $n$, let $\Theta\in H^2(X,\mathbb{C})=\wedge^2H^1(X,\mathbb{C})$ and $c\in\mathbb{C}$. Write $\theta(y)=D_y\Theta\in H^1(X,\mathbb{C})$ for the contraction of $\Theta$ with $y\in H^1(\hat X,\mathbb{C})\cong H^1(X,\mathbb{C})^*$. Then:
--
--   1. $\exp(c\Theta)=\sum_k c^k\Theta^k/k!$ is an even pure spinor: it lies in $H^{\mathrm{ev}}(X,\mathbb{C})$, is nonzero, and its annihilator $W=\{v\in V_{\mathbb{C}}: m_v(\exp(c\Theta))=0\}$ has dimension $2n$;
--   2. a vector $v=(w,t)\in V_{\mathbb{C}}=H^1(X,\mathbb{C})\oplus H^1(\hat X,\mathbb{C})$ lies in $W$ if and only if
--   $$w=-c\,\theta(t).$$
--
--   With $c=\sqrt{-d}$ and $c=-\sqrt{-d}$ this is the description (2.4.6) of the maximal isotropic subspaces $W_1,W_2$ attached to the pure spinors $\exp(u)$ and $\exp(\bar u)$, $u=\sqrt{-d}\,\Theta$: the two points where the secant line $\mathbb{P}(P)$ meets the spinor variety.
--
--   **Formalization Note.** Stated for an arbitrary $2$-form and arbitrary complex $c$; the source uses $c=\pm\sqrt{-d}$ and an ample $\Theta$.
-- source:
--   E. Markman, Cycles on abelian 2n-folds of Weil type from secant sheaves on abelian n-folds, arXiv:2502.03415v2 (8 Jun 2025), https://arxiv.org/abs/2502.03415

import Mathlib
import Definitions.Def_MarkmanSecant

open MarkmanSecant
open scoped ExteriorAlgebra

namespace MarkmanSecant

theorem expS_isEvenPureSpinor_annih (n : ℕ) (Θ : Spinor n) (hΘ : Θ ∈ ⋀[ℂ]^2 (H1 n)) (c : ℂ) :
    IsEvenPureSpinor (expS (c • Θ)) ∧
      ∀ v : VC n, v ∈ annih (expS (c • Θ)) ↔ wPart v = -(c • theta Θ (tPart v)) := by sorry

end MarkmanSecant
