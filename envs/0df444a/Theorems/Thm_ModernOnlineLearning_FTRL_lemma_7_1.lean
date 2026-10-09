-- Prove2me | Theorems.Thm_ModernOnlineLearning_FTRL_lemma_7_1
-- name    : ModernOnlineLearning.FTRL.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:59.676383+00:00
-- url     : https://prove2.me/theorems/b462e340-8752-419c-9499-e2e1283d7337
-- title:
--   Lemma 7.1, p. 100 — exact FTRL regret identity
-- statement:
--   Let $V$ be closed and nonempty, and let $x_t$ minimize $F_t(z)=\psi_t(z)+\sum_{i=1}^{t-1}\ell_i(z)$ over $V$ for rounds $t=1,\ldots,T+1$. For every comparator $u$ in the ambient space,
--   $$\sum_{t=1}^{T}(\ell_t(x_t)-\ell_t(u))=\psi_{T+1}(u)-\psi_1(x_1)+\sum_{t=1}^{T}\bigl(F_t(x_t)-F_{t+1}(x_{t+1})+\ell_t(x_t)\bigr)+F_{T+1}(x_{T+1})-F_{T+1}(u).$$
--   The identity separates comparator regularization from the changes in successive regularized objectives and is the algebraic starting point for FTRL regret bounds.
--
--   **Formalization Note** $\psi_1(x_1)$ is the book's $\min_{z\in V}\psi_1(z)$ because the first-round objective is $F_1=\psi_1$. Losses are real-valued. The book's final sentence, that $\psi_{T+1}$ does not change the first $T$ iterates, follows directly from the run definition and is not included in the Lean equality.
-- source:
--   Orabona, arXiv:1912.13213v10, Lemma 7.1, p. 100

import Mathlib
import Definitions.Def_ModernOnlineLearning_FTRL_Defs

set_option autoImplicit false

namespace ModernOnlineLearning.FTRL

/-- Orabona, Lemma 7.1, p. 100: the exact FTRL regret identity. -/
theorem lemma_7_1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (hVclosed : IsClosed V) (hVnonempty : V.Nonempty)
    (ψ ℓ : ℕ → E → ℝ) (x : ℕ → E) (T : ℕ)
    (hRun : IsFTRLRunUpTo V ψ ℓ x T) (u : E) :
    (∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u)) =
      ψ (T + 1) u - ψ 1 (x 1) +
      (∑ t ∈ Finset.Icc 1 T,
        (F ψ ℓ t (x t) - F ψ ℓ (t + 1) (x (t + 1)) + ℓ t (x t))) +
      F ψ ℓ (T + 1) (x (T + 1)) - F ψ ℓ (T + 1) u := by sorry

end ModernOnlineLearning.FTRL
