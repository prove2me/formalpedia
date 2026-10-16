-- Prove2me | Theorems.Thm_NeedPersuasion_FullInfo_lemma_3
-- name    : NeedPersuasion.FullInfo.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:07.751616+00:00
-- url     : https://prove2.me/theorems/688acbc7-7422-4c5b-bc5c-01e336fceffc
-- title:
--   Lemma 3, p. 36 — for π ∈ Π_AP and k > q: λ_H^{k−q} π_q ≤ π_k ≤ λ^{k−q} π_q; π_k ∈ (0, 1) when λ_H > 0
-- statement:
--   Assume the standing assumptions of the model and let $\pi\in\Pi_{AP}$ be an admission policy. Then for all $k>q$ in $\mathbb N_0$,
--   $$\lambda_H^{\,k-q}\,\pi_q\;\le\;\pi_k\;\le\;\lambda^{k-q}\,\pi_q .$$
--   In particular, if $\lambda_H>0$, then $0<\pi_k<1$ for every $k\in\mathbb N_0$.
--
--   The two-sided geometric sandwich follows the detailed-balance constraints step by step; it is the basic comparison tool behind every perturbation and stochastic-dominance argument of the paper.
-- source:
--   arXiv:2005.07253v3, Lemma 3, p. 36

import Mathlib
import Definitions.Def_NeedPersuasion_FullInfo_Model

namespace NeedPersuasion.FullInfo

theorem lemma_3 (M : Model) (hM : M.Standing) (π : ℕ → ℝ) (hπ : π ∈ PiAP M) :
    (∀ q k : ℕ, q < k → M.lamH ^ (k - q) * π q ≤ π k ∧ π k ≤ M.lam ^ (k - q) * π q) ∧
      (0 < M.lamH → ∀ k : ℕ, 0 < π k ∧ π k < 1) := by sorry

end NeedPersuasion.FullInfo
