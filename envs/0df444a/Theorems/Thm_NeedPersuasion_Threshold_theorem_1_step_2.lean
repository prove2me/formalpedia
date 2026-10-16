-- Prove2me | Theorems.Thm_NeedPersuasion_Threshold_theorem_1_step_2
-- name    : NeedPersuasion.Threshold.theorem_1_step_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:03.512296+00:00
-- url     : https://prove2.me/theorems/77de088c-c4aa-482b-9618-6b5805eeabab
-- title:
--   App. A, proof of Theorem 1, pp. 35–36 — a threshold structure with threshold above m_fi is Pareto-dominated within Π_SM
-- statement:
--   Work in the model of Anunrojwong, Iyer and Manshadi under its standing assumptions. Let $\pi\in\Pi_{\mathsf{SM}}$ be a signaling mechanism with a threshold structure (Definition 2) whose threshold is **not** at most the full-information threshold $m_{\mathsf{fi}}$: either the threshold is $\infty$ ($\pi_{k+1}=\lambda\pi_k$ for every $k$), or it is $x=m+a>m_{\mathsf{fi}}$. Then some $\hat\pi\in\Pi_{\mathsf{SM}}$ Pareto-dominates $\pi$:
--   $$W_{\mathsf L}(\hat\pi)\ge W_{\mathsf L}(\pi),\quad W_{\mathsf H}(\hat\pi)\ge W_{\mathsf H}(\pi),\quad\text{with at least one inequality strict}.$$
--
--   This is the second step of the proof of Theorem 1: among threshold mechanisms, only those whose threshold does not exceed $m_{\mathsf{fi}}$ can be Pareto-efficient.
--
--   **Formalization Note** "Threshold $x>m_{\mathsf{fi}}$, where we allow $m=\infty$" is encoded as: $\pi$ has a threshold structure and there is no finite $m$ at which $\pi$ has a threshold structure with $m+a\le m_{\mathsf{fi}}$.
-- source:
--   arXiv:2005.07253v3, App. A, proof of Theorem 1, pp. 35–36

import Mathlib
import Definitions.Def_NeedPersuasion_Threshold_Model

namespace NeedPersuasion.Threshold

theorem theorem_1_step_2 (M : Model) (hM : M.Standing) (π : ℕ → ℝ) (hπ : π ∈ PiSM M)
    (hT : HasThresholdStructure M π) (hx : ¬ HasThresholdAtMost M π (mfi M)) :
    ∃ π' ∈ PiSM M, Dominates M π' π := by sorry

end NeedPersuasion.Threshold
