-- Prove2me | Theorems.Thm_Micromobility_Transient_policy_cost_eq_obj41
-- name    : Micromobility.Transient.policy_cost_eq_obj41
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:17.957754+00:00
-- url     : https://prove2.me/theorems/8f98a5c0-cca0-4bc4-a2b3-f2fa6b89c681
-- title:
--   §4.1, p. 26 — the cost of the policy π̃ equals the optimal value of (4.1)
-- statement:
--   Fix a state $\breve x \in \breve X$, a transient horizon $T \ge 0$, and a minimizer $\tilde a = (\tilde a^0, \dots, \tilde a^T) \in \hat A^{T+1}$ of the program (4.1). Let $\tilde\pi$ be the policy (4.2)–(4.3), which plays $\tilde a^k$ in period $k < T$ and $\tilde a^T$ in every later period, and let $\hat V_{\tilde\pi}(\breve x)$ be its discounted cost from $\breve x$. Then
--   $$\hat V_{\tilde\pi}(\breve x) = \sum_{k=0}^{T-1}\gamma^k\big(\hat c_2(\breve x^k, \tilde a^k) + \hat N(\tilde a^k)\big) + \gamma^T \hat c_2(\breve x^T, \tilde a^T) + \frac{\gamma^T}{1-\gamma}\big(\gamma\hat c_2(\breve x^{T+1}, \tilde a^T) + \hat N(\tilde a^T)\big),$$
--   the optimal value of (4.1).
--
--   The identity holds because the mean-field model is deterministic: once $\tilde a^T$ is repeated, every later period costs the same. It converts the optimality gap of $\tilde\pi$ into a statement about the program (4.1).
--
--   **Formalization Note.** The hypothesis that $\tilde a$ minimizes (4.1) is kept, as the paper states the identity for the solution of (4.1); the identity in fact holds for every $\tilde a \in \hat A^{T+1}$.
-- source:
--   Akturk, Candogan, Gupta, Managing Resources for Shared Micromobility: Approximate Optimality in Large-Scale Systems, SSRN 4155841 (version of 2024-05-22), p. 26, §4.1, sentence after (4.3)

import Mathlib
import Definitions.Def_Micromobility_Transient_Setting

namespace Micromobility.Transient
theorem policy_cost_eq_obj41 {ê : ℕ} (M : Model ê) (hM : M.Standing)
    (T : ℕ) (x : State ê) (hx : M.InX x)
    (ã : Fin (T + 1) → Action ê) (hã : ∀ k, M.InA (ã k))
    (hmin : ∀ a' : Fin (T + 1) → Action ê, (∀ k, M.InA (a' k)) → M.obj41 x T ã ≤ M.obj41 x T a') :
    M.J x (policySeq T ã) = M.obj41 x T ã := by sorry
end Micromobility.Transient
