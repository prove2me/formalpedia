-- Prove2me | Theorems.Thm_NeedPersuasion_Threshold_theorem_1_dichotomy
-- name    : NeedPersuasion.Threshold.theorem_1_dichotomy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:04:52.236553+00:00
-- url     : https://prove2.me/theorems/f44c88e4-f7fb-4d5b-a79b-abfdc79fe2fa
-- title:
--   App. A, proof of Theorem 1, p. 35 — no leave-then-join pattern forces one of the two threshold structures
-- statement:
--   Work in the model of Anunrojwong, Iyer and Manshadi under its standing assumptions, and let $\pi\in\Pi_{\mathsf{AP}}$. Suppose that for every $m\ge0$,
--   $$\pi_{m+1}<\lambda\pi_m\;\Longrightarrow\;\pi_{m+2}=\lambda_{\mathsf H}\pi_{m+1}.$$
--   Then $\pi$ has one of the following two structures:
--   1. $\pi_{m+1}=\lambda\pi_m$ for all $m\ge0$; or
--   2. there is $m\ge0$ with $\pi_{k+1}=\lambda\pi_k$ for $k<m$, $\pi_{m+1}<\lambda\pi_m$, and $\pi_{k+1}=\lambda_{\mathsf H}\pi_k$ for all $k>m$.
--
--   Combined with the first step of the proof of Theorem 1, this shows that every Pareto-efficient signaling mechanism has a threshold structure (with threshold $\infty$ in the first case and in $[m,m+1]$ in the second).
-- source:
--   arXiv:2005.07253v3, App. A, proof of Theorem 1, p. 35 (paragraph after the first step)

import Mathlib
import Definitions.Def_NeedPersuasion_Threshold_Model

namespace NeedPersuasion.Threshold

theorem theorem_1_dichotomy (M : Model) (hM : M.Standing) (π : ℕ → ℝ) (hπ : π ∈ PiAP M)
    (h : ∀ m : ℕ, π (m + 1) < M.lam * π m → π (m + 2) = M.lamH * π (m + 1)) :
    (∀ m : ℕ, π (m + 1) = M.lam * π m) ∨
      ∃ m : ℕ, (∀ k, k < m → π (k + 1) = M.lam * π k) ∧ π (m + 1) < M.lam * π m ∧
        ∀ k, m < k → π (k + 1) = M.lamH * π k := by sorry

end NeedPersuasion.Threshold
