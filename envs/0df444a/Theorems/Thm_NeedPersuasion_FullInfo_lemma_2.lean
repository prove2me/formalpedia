-- Prove2me | Theorems.Thm_NeedPersuasion_FullInfo_lemma_2
-- name    : NeedPersuasion.FullInfo.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:17.638203+00:00
-- url     : https://prove2.me/theorems/8e9ece3b-95d2-43de-aee6-0f4f3a20b2b8
-- title:
--   Lemma 2, p. 14 — for λ < 1, or λ = 1 with u_L, u_H → −∞, W(·, θ) attains its maximum over Π_SM and over Π_AP
-- statement:
--   Assume the standing assumptions, and assume that the welfare of the H users under the H-only queue is finite: $\sum_{n}\lambda_H^n u_H(n)$ converges. Suppose that either $\lambda<1$, or $u_L(k)\to-\infty$ and $u_H(k)\to-\infty$ as $k\to\infty$. Then for every $\theta\in[0,1]$ there is a signaling mechanism $\pi\in\Pi_{SM}$ with
--   $$W(\pi',\theta)\le W(\pi,\theta)\qquad\text{for all }\pi'\in\Pi_{SM},$$
--   and likewise there is an admission policy maximizing $W(\cdot,\theta)$ over $\Pi_{AP}$.
--
--   Existence of maximizers is what makes the scalarized problems $\max W(\cdot,\theta)$ meaningful, and it is used to show that every non-efficient admission policy is dominated by a Pareto-efficient one.
--
--   **Formalization Note** The summability hypothesis is added: it is equivalent to $\Pi_{AP}\neq\emptyset$ when $\lambda_H>0$ (every $\pi\in\Pi_{AP}$ has $\pi_n\ge\lambda_H^n\pi_0$), and the paper treats all welfare values as finite. The paper writes "$\lim_{n\to\infty}u_i(k)=-\infty$", read as $u_i(k)\to-\infty$ as $k\to\infty$.
-- source:
--   arXiv:2005.07253v3, Lemma 2, p. 14

import Mathlib
import Definitions.Def_NeedPersuasion_FullInfo_Model

namespace NeedPersuasion.FullInfo

theorem lemma_2 (M : Model) (hM : M.Standing)
    (hFin : Summable (fun n : ℕ => M.lamH ^ n * M.uH n))
    (hExist : M.lam < 1 ∨
      (Filter.Tendsto M.uL Filter.atTop Filter.atBot ∧
        Filter.Tendsto M.uH Filter.atTop Filter.atBot))
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    (∃ π ∈ PiSM M, ∀ π' ∈ PiSM M, W M θ π' ≤ W M θ π) ∧
      (∃ π ∈ PiAP M, ∀ π' ∈ PiAP M, W M θ π' ≤ W M θ π) := by sorry

end NeedPersuasion.FullInfo
