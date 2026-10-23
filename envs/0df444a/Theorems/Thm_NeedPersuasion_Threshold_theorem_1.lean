-- Prove2me | Theorems.Thm_NeedPersuasion_Threshold_theorem_1
-- name    : NeedPersuasion.Threshold.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:04:59.945984+00:00
-- url     : https://prove2.me/theorems/39d1c79b-61cb-4536-b8d4-712ccafde557
-- title:
--   Theorem 1, p. 14 — every Pareto-efficient signaling mechanism has a threshold structure with threshold ≤ m_fi
-- statement:
--   **Theorem 1** (Threshold structure of Pareto-efficient signaling mechanisms). Work in the model of Anunrojwong, Iyer and Manshadi under its standing assumptions ($\lambda_{\mathsf L}>0$, $\lambda_{\mathsf H}\ge0$, $\lambda=\lambda_{\mathsf L}+\lambda_{\mathsf H}\le1$, utilities positive at $0$, eventually negative, strictly decreasing, and with non-increasing increments for type $\mathsf L$). Let $m_{\mathsf{fi}}$ be the smallest $k$ with $u_{\mathsf L}(k)<0$.
--
--   If $\pi\in\Pi_{\mathsf{SM}}$ is Pareto-efficient within $\Pi_{\mathsf{SM}}$, then $\pi$ has a threshold structure with a finite $m\in\mathbb N_0$,
--   $$\pi_{k+1}=\lambda\pi_k\ (k<m),\qquad\pi_{k+1}=\lambda_{\mathsf H}\pi_k\ (k>m),$$
--   whose threshold satisfies
--   $$x=m+\frac{\pi_{m+1}-\lambda_{\mathsf H}\pi_m}{\lambda_{\mathsf L}\pi_m}\;\le\;m_{\mathsf{fi}}.$$
--
--   In words: under every Pareto-efficient obedient signaling mechanism, low-need users are told to join below some queue length, to leave above it, and are randomized only at that one queue length; and they are never asked to join more often than under full information. The structural results on admission policies and the welfare comparisons of the paper (Theorems 3–6, Propositions 1 and 3) are built on this reduction to a one-parameter family.
--
--   **Formalization Note** The conclusion is stated as the conjunction of "threshold structure" and "threshold at most $m_{\mathsf{fi}}$"; the second already excludes the threshold $\infty$ and implies the first. Pareto efficiency is Definition 1 (no dominating mechanism in $\Pi_{\mathsf{SM}}$), not maximization of a weighted welfare. $\Pi_{\mathsf{AP}}$ includes finite welfare (see the model file). The theorem holds at $\lambda=1$; no assumption $\lambda<1$ is made.
-- source:
--   arXiv:2005.07253v3, Theorem 1, p. 14; proof in App. A, pp. 34–36

import Mathlib
import Definitions.Def_NeedPersuasion_Threshold_Model

namespace NeedPersuasion.Threshold

theorem theorem_1 (M : Model) (hM : M.Standing) (π : ℕ → ℝ)
    (hπ : ParetoEfficientIn M (PiSM M) π) :
    HasThresholdStructure M π ∧ HasThresholdAtMost M π (mfi M) := by sorry

end NeedPersuasion.Threshold
