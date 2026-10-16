-- Prove2me | Theorems.Thm_NeedPersuasion_Threshold_theorem_1_step_1
-- name    : NeedPersuasion.Threshold.theorem_1_step_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:04:51.378999+00:00
-- url     : https://prove2.me/theorems/06e4e020-bc54-4640-a437-4bbab961c837
-- title:
--   App. A, proof of Theorem 1, p. 34 — leaving at m and joining at m + 1 is Pareto-dominated within Π_SM
-- statement:
--   Work in the model of Anunrojwong, Iyer and Manshadi under its standing assumptions. Let $\pi\in\Pi_{\mathsf{SM}}$ be a signaling mechanism and suppose there is $m\ge0$ with
--   $$\pi_{m+1}<\lambda\pi_m\qquad\text{and}\qquad\lambda_{\mathsf H}\pi_{m+1}<\pi_{m+2},$$
--   that is, an arriving low-need user is asked to leave with positive probability at queue length $m$ and asked to join with positive probability at queue length $m+1$. Then some $\hat\pi\in\Pi_{\mathsf{SM}}$ Pareto-dominates $\pi$:
--   $$W_{\mathsf L}(\hat\pi)\ge W_{\mathsf L}(\pi),\quad W_{\mathsf H}(\hat\pi)\ge W_{\mathsf H}(\pi),\quad\text{with at least one inequality strict}.$$
--   In particular $\pi$ is not Pareto-efficient within $\Pi_{\mathsf{SM}}$.
--
--   This is the first step of the proof of Theorem 1: an interior "leave, then join" pattern is never efficient.
--
--   **Formalization Note** The page opens with "Let $\pi\in\Pi_{\mathsf{AP}}$", but the argument keeps (JOIN) and (LEAVE) for $\hat\pi$ only because $\pi$ satisfies them; the statement is therefore posed for $\pi\in\Pi_{\mathsf{SM}}$, as the page's own conclusion ("cannot be Pareto-efficient within $\Pi_{\mathsf{SM}}$") requires.
-- source:
--   arXiv:2005.07253v3, App. A, proof of Theorem 1, first paragraph, pp. 34–35

import Mathlib
import Definitions.Def_NeedPersuasion_Threshold_Model

namespace NeedPersuasion.Threshold

theorem theorem_1_step_1 (M : Model) (hM : M.Standing) (π : ℕ → ℝ) (hπ : π ∈ PiSM M) (m : ℕ)
    (hleave : π (m + 1) < M.lam * π m) (hjoin : M.lamH * π (m + 1) < π (m + 2)) :
    ∃ π' ∈ PiSM M, Dominates M π' π := by sorry

end NeedPersuasion.Threshold
