-- Prove2me | Theorems.Thm_HarrisContact_MeanSize_theorem_7_6
-- name    : HarrisContact.MeanSize.theorem_7_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:27:15.658017+00:00
-- url     : https://prove2.me/theorems/db74c4f6-586a-49ab-a783-436bd1bbb381
-- title:
--   Theorem 7.6, p. 982 — if $\lambda_k/\mu<k/(2d-1)$ then $\int_0^\infty m_t(\xi)\,dt<\infty$
-- statement:
--   Let $(\xi_t)$ be the contact process on $Z_d$, $d\ge1$: each occupied site becomes vacant at rate $\mu>0$, and a vacant site with $k$ occupied neighbours becomes occupied at rate $\lambda_k$, where $\lambda_0=0$ and $\lambda_k\ge0$ for $k\le 2d$. Let $m_t(\xi)$ be the expected number of occupied sites at time $t$ when the process starts from the finite set $\xi$. If
--   $$\frac{\lambda_k}{\mu}<\frac{k}{2d-1},\qquad k=1,\dots,2d,$$
--   then for every finite $\xi\subset Z_d$,
--   $$\int_0^\infty m_t(\xi)\,dt<\infty .$$
--
--   The total expected occupation time of all sites is finite: in this subcritical regime the process not only dies out but does so fast enough on average. With Lemma 4.11 it gives $m_t(\xi)\to0$ (Remark 7.12).
--
--   **Formalization Note** The standing hypotheses of the contact process (Harris, §2(b), p. 971; §3, p. 972) are written as binders: $d \ge 1$, $\mu \ge 0$, $\lambda_0 = 0$ and $\lambda_k \ge 0$ for $0 \le k \le 2d$. Rates $\lambda_k$ with $k > 2d$ never enter the model, and no hypothesis mentions them. The hypothesis $\mu>0$ is implicit in the paper's ratio $\lambda_k/\mu$ and is added explicitly: in Lean $\lambda_k/0=0$, so without it the rate condition would hold for every $\lambda$ at $\mu=0$, where the process never shrinks and the conclusion is false. $2d-1$ is the real number $2d-1\ge1$. The process is the countable-state chain on finite configurations of §4 (p. 975), with transition function the minimal solution $P_t$ of the backward equations for the rates (4.4)–(4.5); $m_t(\xi)=\sum_\eta P_t(\xi,\eta)\,|\eta|$ is an extended nonnegative real, so a divergent sum is $+\infty$, never $0$. The integral is the Lebesgue integral of a $[0,\infty]$-valued function over $(0,\infty)$, so a divergent integral is $+\infty$.
-- source:
--   Harris (Ann. Probab. 2, 1974), Theorem 7.6, p. 982

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.MeanSize

/-- Harris (Ann. Probab. 2, 1974), Theorem 7.6, p. 982: if `λ_k/μ < k/(2d − 1)` for `k = 1, …, 2d`, then
`∫_0^∞ m_t(ξ) dt < ∞` for every finite `ξ`. -/
theorem theorem_7_6 {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 < μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (hsub : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * d → lam k / μ < k / (2 * (d : ℝ) - 1)) :
    ∀ ξ : HarrisContact.Extinction.Config d, ∫⁻ t in Set.Ioi (0 : ℝ), HarrisContact.Extinction.meanSize μ lam t ξ < ∞ := by sorry
end HarrisContact.MeanSize
