-- Prove2me | Theorems.Thm_InterimTesting_NotProficient_lemma_1
-- name    : InterimTesting.NotProficient.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:39.190876+00:00
-- url     : https://prove2.me/theorems/ab6de60c-50cd-42e9-bfc9-ed4ad5405a4e
-- title:
--   Lemma 1, p. 12 (PDF 12) — second-period effort is 1 iff π ≥ 𝒯1(S1), and 0 otherwise
-- statement:
--   Let $\pi\ge0$ be the merit-based incentive and $p\in[0,1]$ the teachers' posterior probability that the school is proficient at midyear. The teachers' optimal second-period effort (the largest maximizer over $[0,1]$) is
--   $$e_1^*=\begin{cases}0,&\pi<\mathcal T_1,\\1,&\mathcal T_1\le\pi,\end{cases}\qquad \mathcal T_1=\frac{1}{A((1-\mu)p+\mu)} .$$
--
--   The second-period effort is bang-bang, with an incentive threshold that falls as the posterior rises.
--
--   **Formalization Note** $\mathcal T_1(S_1)$ depends on $S_1$ only through the posterior, so the statement is made for every $p\in[0,1]$ (`T1p θ p`). It uses $A>0$, $0<\mu<1$ from the standing assumptions.
-- source:
--   Virudachalam, Savin & Steinberg, Too Much Information: When Does Additional Testing Benefit Schools?, SSRN 3884543 (version of November 3, 2022), p. 12 (PDF 12), Lemma 1, (11); expanded p. A4 (PDF 30), (A6)–(A8)

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model

namespace InterimTesting.NotProficient

/-- Lemma 1, p. 12 (expanded (A6), p. A4): the optimal second-period effort is `1` if
`π ≥ 𝒯1(S1)` and `0` if `π < 𝒯1(S1)`, where `𝒯1` depends on `S1` through the posterior `p`. -/
theorem lemma_1 (θ : Params) (hθ : θ.Standing) (π p : ℝ) (hπ : 0 ≤ π)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    e1Star θ π p = if T1p θ p ≤ π then 1 else 0 := by sorry

end InterimTesting.NotProficient
