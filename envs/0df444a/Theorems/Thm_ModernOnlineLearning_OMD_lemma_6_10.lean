-- Prove2me | Theorems.Thm_ModernOnlineLearning_OMD_lemma_6_10
-- name    : ModernOnlineLearning.OMD.lemma_6_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:37:05.932443+00:00
-- url     : https://prove2.me/theorems/a0dc0ce6-2706-475d-9447-98d6c0bcad39
-- title:
--   Lemma 6.10, p. 67 — three-part one-step OMD inequality
-- statement:
--   Under the assumptions of Lemma 6.10 and an online mirror descent run, let $u\in V$. On every round $t=1,\ldots,T$, with positive step size $\eta_t$ and selected subgradient $g_t$,
--
--   $$\begin{aligned}
--   \eta_t(\ell_t(x_t)-\ell_t(u))
--   &\le \eta_t\langle g_t,x_t-u\rangle\\
--   &\le B_\psi(u;x_t)-B_\psi(u;x_{t+1})-B_\psi(x_{t+1};x_t)
--      +\eta_t\langle g_t,x_t-x_{t+1}\rangle\\
--   &\le B_\psi(u;x_t)-B_\psi(u;x_{t+1})
--      +\frac{\eta_t^2}{2\lambda}\|g_t\|_*^2.
--   \end{aligned}$$
--
--   This is the one-step estimate that telescopes to the regret bound in Theorem 6.11.
--
--   **Formalization Note** The primal norm is the norm on $E$, and $\|g_t\|_*$ is the continuous dual's operator norm. Subgradient inequalities are relative to $V$. The setting assumes the book's condition (6.5) or (6.6); $\lambda>0$ and $\eta_t>0$ make the displayed divisions meaningful. The update's existence and uniqueness are a separate item from this lemma.
-- source:
--   Orabona, arXiv:1912.13213v10, Lemma 6.10, inequality clause, p. 67

import Mathlib
import Definitions.Def_ModernOnlineLearning_OMD_Defs

namespace ModernOnlineLearning.OMD

/-- The full three-part one-step inequality in Lemma 6.10, p. 67, for every
round of Algorithm 6.1 under "(6.5) or (6.6)". -/
theorem lemma_6_10 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (X V : Set E) (ψ : E → ℝ) (lam : ℝ)
    (hsetting : IsOMDSetting X V ψ lam)
    (T : ℕ) (η : ℕ → ℝ) (ℓ : ℕ → E → ℝ)
    (x : ℕ → E) (g : ℕ → E →L[ℝ] ℝ)
    (hrun : IsOMDRun T X V ψ η ℓ x g) :
    ∀ t ∈ Finset.Icc 1 T, ∀ u ∈ V,
      η t * (ℓ t (x t) - ℓ t u) ≤ η t * g t (x t - u) ∧
      η t * g t (x t - u) ≤
        BeckTeboulleMD.EMDA.bregman ψ u (x t) -
        BeckTeboulleMD.EMDA.bregman ψ u (x (t + 1)) -
        BeckTeboulleMD.EMDA.bregman ψ (x (t + 1)) (x t) +
        η t * g t (x t - x (t + 1)) ∧
      BeckTeboulleMD.EMDA.bregman ψ u (x t) -
        BeckTeboulleMD.EMDA.bregman ψ u (x (t + 1)) -
        BeckTeboulleMD.EMDA.bregman ψ (x (t + 1)) (x t) +
        η t * g t (x t - x (t + 1)) ≤
        BeckTeboulleMD.EMDA.bregman ψ u (x t) -
        BeckTeboulleMD.EMDA.bregman ψ u (x (t + 1)) +
        (η t) ^ 2 / (2 * lam) * ‖g t‖ ^ 2 := by sorry

end ModernOnlineLearning.OMD
