-- Prove2me | Theorems.Thm_NeedPersuasion_Threshold_lemma_3
-- name    : NeedPersuasion.Threshold.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:04:51.455848+00:00
-- url     : https://prove2.me/theorems/c6df22f5-886f-4321-9130-ba59520524c2
-- title:
--   Lemma 3, p. 36 — for π ∈ Π_AP and k > q: λ_H^{k−q} π_q ≤ π_k ≤ λ^{k−q} π_q; if λ_H > 0, every π_k ∈ (0, 1)
-- statement:
--   Work in the model of Anunrojwong, Iyer and Manshadi under its standing assumptions, and let $\pi\in\Pi_{\mathsf{AP}}$ be an admission policy, so that $\pi$ is a probability distribution on $\mathbb N_0$ with $\lambda_{\mathsf H}\pi_n\le\pi_{n+1}\le\lambda\pi_n$ for every $n$.
--
--   1. For all $k>q$ in $\mathbb N_0$,
--   $$\lambda_{\mathsf H}^{\,k-q}\,\pi_q\;\le\;\pi_k\;\le\;\lambda^{k-q}\,\pi_q .$$
--   2. If $\lambda_{\mathsf H}>0$, then $0<\pi_k<1$ for every $k\in\mathbb N_0$.
--
--   The two-sided geometric sandwich lets one compare the tail of any admission policy with the tails of the extreme policies "everyone joins" and "only high-need users join"; it is the comparison used in the proof of Theorem 1 to show that truncating a threshold policy at $m_{\mathsf{fi}}$ is stochastically dominated by the original.
-- source:
--   arXiv:2005.07253v3, Lemma 3, p. 36

import Mathlib
import Definitions.Def_NeedPersuasion_Threshold_Model

namespace NeedPersuasion.Threshold

theorem lemma_3 (M : Model) (hM : M.Standing) (π : ℕ → ℝ) (hπ : π ∈ PiAP M) :
    (∀ k q : ℕ, q < k → M.lamH ^ (k - q) * π q ≤ π k ∧ π k ≤ M.lam ^ (k - q) * π q) ∧
      (0 < M.lamH → ∀ k : ℕ, 0 < π k ∧ π k < 1) := by sorry

end NeedPersuasion.Threshold
