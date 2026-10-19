-- Prove2me | Theorems.Thm_InfFisher_Linear_S_eq_cone_inter_T
-- name    : InfFisher.Linear.S_eq_cone_inter_T
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:42.006175+00:00
-- url     : https://prove2.me/theorems/fa2e9629-eace-4a4a-b7ff-6645111d5091
-- title:
--   Proof of Theorem 4, (A.8) — two-buyer region as a cone section
-- statement:
--   Consider two adjacent normalized linear valuations $v_1(\theta)=c_1\theta+d_1$ and $v_2(\theta)=c_2\theta+d_2$ with $2\ge d_1\ge d_2\ge0$. Let $S$ be the region of $(z,w)$ for which some $a\in[0,1]$ satisfies $z\le c_1a^2/2+d_1a$, $w\le-c_2a^2/2-d_2a$, $0\le z\le1$, $-1\le w\le0$, and $z+w\ge0$. Then
--
--   $$S=\{(z,w):0\le z\le1,\ -1\le w\le0,\ z+w\ge0,\ \exists(s,t),\ s^2\le t,\ (z,w)=G(s,t)\},$$
--
--   where $G(s,t)=(d_1s+c_1t/2,-d_2s-c_2t/2)$. This is the pairwise geometric identification used to replace the breakpoint inequalities by parabolic cone constraints in Theorem 4.
--
--   **Formalization Note** The right side writes the paper's $\operatorname{conv}(\bar\Gamma)\cap T$ identification as $G\mathcal C\cap T$. It includes the tied intercept case.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, proof of Theorem 4, (A.8), pp. a11–a12 (PDF 46–47)

import Mathlib
import Definitions.Def_InfFisher_Linear_Setting

namespace InfFisher.Linear

/-- Gao–Kroer, proof of Theorem 4, (A.8): the two-buyer region is a transformed parabolic cone cut by `T`. -/
theorem S_eq_cone_inter_T (c₁ d₁ c₂ d₂ : ℝ)
    (h₁ : c₁ / 2 + d₁ = 1) (h₂ : c₂ / 2 + d₂ = 1)
    (hd : d₂ ≤ d₁) (hd₁ : d₁ ≤ 2) (hd₂ : 0 ≤ d₂) :
    {q : ℝ × ℝ | ∃ a ∈ Set.Icc (0 : ℝ) 1,
      q.1 ≤ c₁ / 2 * a ^ 2 + d₁ * a ∧
      q.2 ≤ -(c₂ / 2) * a ^ 2 - d₂ * a ∧
      q.1 ∈ Set.Icc (0 : ℝ) 1 ∧
      q.2 ∈ Set.Icc (-1 : ℝ) 0 ∧ 0 ≤ q.1 + q.2} =
    {q : ℝ × ℝ |
      q.1 ∈ Set.Icc (0 : ℝ) 1 ∧
      q.2 ∈ Set.Icc (-1 : ℝ) 0 ∧ 0 ≤ q.1 + q.2 ∧
      ∃ s t : ℝ, s ^ 2 ≤ t ∧
        q = (d₁ * s + c₁ / 2 * t, -d₂ * s - c₂ / 2 * t)} := by sorry

end InfFisher.Linear
