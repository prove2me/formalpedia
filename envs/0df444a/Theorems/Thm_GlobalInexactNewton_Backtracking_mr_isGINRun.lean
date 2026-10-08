-- Prove2me | Theorems.Thm_GlobalInexactNewton_Backtracking_mr_isGINRun
-- name    : GlobalInexactNewton.Backtracking.mr_isGINRun
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:34:53.533983+00:00
-- url     : https://prove2.me/theorems/42370de4-2269-4522-ac6f-b91c9934d32b
-- title:
--   §5, p. 408 — Algorithm MR is a special case of Algorithm GIN
-- statement:
--   Let $E$ be a real normed space and $F:E\to E$. Every run of Algorithm MR with parameters $\eta_{\max}$, $t$, $\theta_{\min}$, $\theta_{\max}$ is a run of Algorithm GIN with the same $t$, the same iterates $x_k$, and the levels $\eta_k$ equal to the final values of the while-loop. That is, $\eta_k\in[0,1)$, and $s_k=x_{k+1}-x_k=\sigma_k(\eta_k)$ satisfies the inexact Newton condition (2.1) and the sufficient decrease condition (2.2) at level $\eta_k$.
--
--   This is how the global convergence results for GIN (Theorems 3.4 and 3.5) transfer to Algorithm MR.
--
--   **Formalization Note** The final level of iteration $k$ is $\eta^{(m_k)}$, the level visited after the loop body has run $m_k$ times. The statement needs no differentiability or finite dimension, so neither is assumed.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), §5, before Theorem 5.2, p. 408

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
open Filter Topology

namespace GlobalInexactNewton.Backtracking

/-- Eisenstat–Walker (1994), §5, before Theorem 5.2, p. 408: Algorithm MR is a special case of
Algorithm GIN. Every run of Algorithm MR is a run of Algorithm GIN with the same `t` and with the
final loop levels `η_k = trialLevel (ηbar k) (θ k) (m k)`. -/
theorem mr_isGINRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (ηmax t θmin θmax : ℝ) (x : ℕ → E) (ηbar : ℕ → ℝ) (σ : ℕ → ℝ → E)
    (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ) (hrun : IsMRRun F ηmax t θmin θmax x ηbar σ θ m) :
    IsGINRun F t x (fun k => trialLevel (ηbar k) (θ k) (m k)) := by sorry

end GlobalInexactNewton.Backtracking
