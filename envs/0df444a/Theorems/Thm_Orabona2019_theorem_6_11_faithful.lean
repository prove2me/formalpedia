-- Prove2me | Theorems.Thm_Orabona2019_theorem_6_11_faithful
-- name    : Orabona2019.theorem_6_11_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T00:30:46.608831+00:00
-- url     : https://prove2.me/theorems/fc5744c8-b284-494c-943f-db5f47a1e2fe
-- title:
--   Theorem 6.11, with the constant-step bound
-- statement:
--   Let $E$ be a finite-dimensional real normed space with dual norm $\|\cdot\|_\star$, $V\subseteq X\subseteq E$ with $V$ non-empty, closed and convex, and $\psi:X\to\mathbb R$ closed, strictly convex, differentiable on $\operatorname{int}X$ and $\lambda$-strongly convex on $V$ ($\lambda>0$), with condition (6.5) or $V\subseteq\operatorname{int}X$; let $B_\psi(a;b)=\psi(a)-\psi(b)-\langle\nabla\psi(b),a-b\rangle$. Run Online Mirror Descent for $T\ge1$ rounds from $x_1\in V\cap\operatorname{int}X$: $g_t$ is a subgradient of $\ell_t$ at $x_t$ and $x_{t+1}\in\operatorname{argmin}_{x\in V}\langle g_t,x\rangle+B_\psi(x;x_t)/\eta_t$, with step sizes $0<\eta_{t+1}\le\eta_t$. Then for all $u\in V$:
--
--   1. $$\sum_{t=1}^T\big(\ell_t(x_t)-\ell_t(u)\big)\le\frac{\max_{1\le t\le T}B_\psi(u;x_t)}{\eta_T}+\frac1{2\lambda}\sum_{t=1}^T\eta_t\|g_t\|_\star^2;$$
--   2. if $\eta_t=\eta$ for all $t=1,\dots,T$, $$\sum_{t=1}^T\big(\ell_t(x_t)-\ell_t(u)\big)\le\frac{B_\psi(u;x_1)}{\eta}+\frac{\eta}{2\lambda}\sum_{t=1}^T\|g_t\|_\star^2.$$
--
--   This is Theorem 6.11 of Orabona's book with both of its conclusions, the basic regret bound of Online Mirror Descent. The existing theorem ModernOnlineLearning.OMD.theorem_6_11 is part 1; part 2 does not follow from it, since $\max_tB_\psi(u;x_t)\ge B_\psi(u;x_1)$.
--
--   **Formalization Note** Losses are real-valued with subgradients relative to $V$; the dual norm is the operator norm on $E\to\mathbb R$.
-- source:
--   Orabona, A Modern Introduction to Online Learning, arXiv:1912.13213v10, p. 67, Theorem 6.11

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting
import Definitions.Def_ModernOnlineLearning_OMD_Defs

open ModernOnlineLearning.OMD

theorem Orabona2019.theorem_6_11_faithful {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (X V : Set E) (ψ : E → ℝ) (lam : ℝ)
    (hsetting : IsOMDSetting X V ψ lam)
    (T : ℕ) (hT : 1 ≤ T) (η : ℕ → ℝ) (ℓ : ℕ → E → ℝ)
    (x : ℕ → E) (g : ℕ → E →L[ℝ] ℝ)
    (hrun : IsOMDRun T X V ψ η ℓ x g)
    (hmono : ∀ t : ℕ, 1 ≤ t → t < T → η (t + 1) ≤ η t) :
    (∀ u ∈ V,
      (∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u)) ≤
        bregmanMax T hT ψ u x / η T +
          (1 / (2 * lam)) * ∑ t ∈ Finset.Icc 1 T, η t * ‖g t‖ ^ 2) ∧
    (∀ η₀ : ℝ, (∀ t ∈ Finset.Icc 1 T, η t = η₀) → ∀ u ∈ V,
      (∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u)) ≤
        BeckTeboulleMD.EMDA.bregman ψ u (x 1) / η₀ +
          (η₀ / (2 * lam)) * ∑ t ∈ Finset.Icc 1 T, ‖g t‖ ^ 2) := by sorry
