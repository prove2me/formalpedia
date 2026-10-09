-- Prove2me | Theorems.Thm_ModernOnlineLearning_OMD_theorem_6_11
-- name    : ModernOnlineLearning.OMD.theorem_6_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:38:00.374651+00:00
-- url     : https://prove2.me/theorems/ad70e6e3-37c8-43d5-ad1f-6639570a5be0
-- title:
--   Theorem 6.11, p. 67 — online mirror descent regret with decreasing steps
-- statement:
--   Let $T\ge1$ and run Algorithm 6.1 on a nonempty closed convex set $V\subseteq\operatorname{int}X$ with a proper, closed regularizer $\psi$ that is $\lambda$-strongly convex on $V$, $\lambda>0$. Let $g_t$ be the selected subgradient of loss $\ell_t$ at $x_t$, and $B_\psi$ the regularizer's Bregman divergence. If $0<\eta_{t+1}\le\eta_t$ for $t<T$, then for every $u\in V$,
--
--   $$\sum_{t=1}^T\bigl(\ell_t(x_t)-\ell_t(u)\bigr)
--   \le\frac{\max_{1\le t\le T}B_\psi(u;x_t)}{\eta_T}
--   +\frac1{2\lambda}\sum_{t=1}^T\eta_t\|g_t\|_*^2.$$
--
--   The theorem controls regret against each fixed competitor using the geometry of $\psi$ and the dual norms of the observed subgradients. Its constant-step conclusion is recorded as a companion item.
--
--   **Formalization Note** The finite maximum is taken over the nonempty round set $\{1,\ldots,T\}$; Lean's total supremum on an empty real set is not used. Steps and strong-convexity modulus are positive. The setting assumes the book's condition (6.5) or (6.6) from Lemma 6.10. Losses are real-valued on $V$ and the chosen subgradients satisfy the relative inequality on $V$.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 6.11, p. 67

import Mathlib
import Definitions.Def_ModernOnlineLearning_OMD_Defs

namespace ModernOnlineLearning.OMD

/-- The first, decreasing-step bound of Theorem 6.11, p. 67. The maximum is
over the nonempty finite set of rounds `1,...,T`. -/
theorem theorem_6_11 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (X V : Set E) (ψ : E → ℝ) (lam : ℝ)
    (hsetting : IsOMDSetting X V ψ lam)
    (T : ℕ) (hT : 1 ≤ T) (η : ℕ → ℝ) (ℓ : ℕ → E → ℝ)
    (x : ℕ → E) (g : ℕ → E →L[ℝ] ℝ)
    (hrun : IsOMDRun T X V ψ η ℓ x g)
    (hmono : ∀ t : ℕ, 1 ≤ t → t < T → η (t + 1) ≤ η t) :
    ∀ u ∈ V,
      (∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u)) ≤
        bregmanMax T hT ψ u x / η T +
          (1 / (2 * lam)) * ∑ t ∈ Finset.Icc 1 T, η t * ‖g t‖ ^ 2 := by sorry

end ModernOnlineLearning.OMD
