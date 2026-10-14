-- Prove2me | Theorems.Thm_Micromobility_Transient_theorem_4_2
-- name    : Micromobility.Transient.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:09:13.310001+00:00
-- url     : https://prove2.me/theorems/a4dfd506-8cf5-4d75-a3d1-6afbb51fbafb
-- title:
--   Theorem 4.2, p. 27 — the transient-horizon policy has optimality gap ≤ γCγᵀ/(1−γ), and ≤ Cγᵀ if q = 0
-- statement:
--   Consider the compact mean-field model under its standing assumptions. Fix a transient horizon $T \ge 0$ and an initial state $\breve x \in \breve X$, let $\tilde a = (\tilde a^0, \dots, \tilde a^T) \in \hat A^{T+1}$ be any minimizer of the program (4.1), and let $\tilde\pi$ be the policy (4.2)–(4.3) that plays $\tilde a^k$ in periods $k < T$ and $\tilde a^T$ in every period $k \ge T$. Write $\hat V_{\tilde\pi}(\breve x)$ for its discounted cost and $\hat V(\breve x)$ for the optimal value. Then
--   $$\hat V_{\tilde\pi}(\breve x) - \hat V(\breve x) \le \frac{\gamma}{1-\gamma}\,C\,\gamma^T,$$
--   where
--   $$C = 2\sum_{e=1}^{\hat e}\Big(n_e\max(c_{0,e}, c_{e,0})(U^e - L^e) + n\max(c_{0,\hat e+e}, c_{\hat e+e,0})(U^{r,e} - L^{r,e})\Big).$$
--   Furthermore, if $q = 0$,
--   $$\hat V_{\tilde\pi}(\breve x) - \hat V(\breve x) \le C\,\gamma^T.$$
--
--   The optimality gap of the transient-horizon policy decays geometrically in the length $T$ of the transient period, uniformly over the initial state, with a constant determined by the rebalancing costs and the action bounds.
--
--   **Formalization Note.** The policy cost is the discounted cost of the action sequence $\tilde a^0, \dots, \tilde a^{T-1}, \tilde a^T, \tilde a^T, \dots$; the bound holds for every minimizer of (4.1) (one exists, since $\hat A^{T+1}$ is compact and the objective continuous). Both bounds use Theorem 4.2's $C$, with the factor $2$ (Proposition H.10 prints $C$ without it, a slip its own proof does not support). The disclosed additions $\gamma \ge 0$ and $c_{e_1,e_2} \ge 0$ are part of the standing assumptions.
-- source:
--   Akturk, Candogan, Gupta, Managing Resources for Shared Micromobility: Approximate Optimality in Large-Scale Systems, SSRN 4155841 (version of 2024-05-22), p. 27, Theorem 4.2 (proof: App. H, pp. A-28–A-34, Propositions H.6 and H.10)

import Mathlib
import Definitions.Def_Micromobility_Transient_Setting

namespace Micromobility.Transient
theorem theorem_4_2 {ê : ℕ} (M : Model ê) (hM : M.Standing)
    (T : ℕ) (x : State ê) (hx : M.InX x)
    (ã : Fin (T + 1) → Action ê) (hã : ∀ k, M.InA (ã k))
    (hmin : ∀ a' : Fin (T + 1) → Action ê, (∀ k, M.InA (a' k)) → M.obj41 x T ã ≤ M.obj41 x T a') :
    M.J x (policySeq T ã) - M.Vhat x ≤ M.γ / (1 - M.γ) * M.Cconst * M.γ ^ T ∧
    (M.q = 0 → M.J x (policySeq T ã) - M.Vhat x ≤ M.Cconst * M.γ ^ T) := by sorry
end Micromobility.Transient
