-- Prove2me | Theorems.Thm_NeedPersuasion_FirstBest_lemma_3
-- name    : NeedPersuasion.FirstBest.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:04.948957+00:00
-- url     : https://prove2.me/theorems/156be202-07b3-4c90-913f-4b05c222c143
-- title:
--   Lemma 3, p. 36 — for π ∈ Π_AP and k > q: λ_H^{k−q} π_q ≤ π_k ≤ λ^{k−q} π_q
-- statement:
--   Let $\pi\in\Pi_{AP}$ be an admission policy. Then for all $k>q$ in $\mathbb N_0$,
--   $$\lambda_H^{\,k-q}\,\pi_q\;\le\;\pi_k\;\le\;\lambda^{k-q}\,\pi_q .$$
--   In particular, if $\lambda_H>0$, then $\pi_k\in(0,1)$ for every $k\in\mathbb N_0$.
--
--   The sandwich is the stochastic-dominance tool used throughout: every admission policy is squeezed between the queue-length laws with arrival rates $\lambda_H$ and $\lambda$.
-- source:
--   arXiv:2005.07253v3, Lemma 3, p. 36

import Mathlib
import Definitions.Def_NeedPersuasion_FirstBest_Model

namespace NeedPersuasion.FirstBest

theorem lemma_3 (M : Model) (hM : M.Standing) (π : ℕ → ℝ) (hπ : π ∈ PiAP M) :
    (∀ k q : ℕ, q < k → M.lamH ^ (k - q) * π q ≤ π k ∧ π k ≤ M.lam ^ (k - q) * π q) ∧
      (0 < M.lamH → ∀ k : ℕ, 0 < π k ∧ π k < 1) := by sorry

end NeedPersuasion.FirstBest
