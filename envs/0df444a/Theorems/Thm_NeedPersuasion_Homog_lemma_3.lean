-- Prove2me | Theorems.Thm_NeedPersuasion_Homog_lemma_3
-- name    : NeedPersuasion.Homog.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:15.089623+00:00
-- url     : https://prove2.me/theorems/bd1ce54c-14d9-41e3-8773-1dabc33e51b9
-- title:
--   Lemma 3, p. 36 — detailed-balance sandwich: λ_H^{k−q} π_q ≤ π_k ≤ λ^{k−q} π_q
-- statement:
--   Consider the congested-service model under its standing assumptions, with arrival rates $\lambda_L$, $\lambda_H$ and total rate $\lambda = \lambda_L + \lambda_H$. Let $\pi \in \Pi_{AP}$ be an admission policy, i.e. a probability distribution on the queue lengths $\mathbb N_0$ with $\lambda_H \pi_n \le \pi_{n+1} \le \lambda\pi_n$ for all $n$. Then for all $q < k$ in $\mathbb N_0$,
--   $$\lambda_H^{k-q}\,\pi_q \;\le\; \pi_k \;\le\; \lambda^{k-q}\,\pi_q .$$
--
--   The lemma compares the stationary distribution at distant queue lengths; it is the source of the stochastic-dominance comparisons used in the proof of Theorem 1.
--
--   **Formalization Note** Only the first sentence of Lemma 3 is posed. Its second sentence ("when $\lambda_H > 0$, $\pi_k \in (0,1)$") is vacuous in this mission's homogeneous setting $\lambda_H = 0$.
-- source:
--   arXiv:2005.07253v3, Lemma 3, p. 36 (first sentence)

import Mathlib
import Definitions.Def_NeedPersuasion_Homog_Model

namespace NeedPersuasion.Homog

theorem lemma_3 (M : Model) (hM : M.Standing) (π : ℕ → ℝ) (hπ : π ∈ PiAP M)
    (q k : ℕ) (hqk : q < k) :
    M.lamH ^ (k - q) * π q ≤ π k ∧ π k ≤ M.lam ^ (k - q) * π q := by sorry

end NeedPersuasion.Homog
