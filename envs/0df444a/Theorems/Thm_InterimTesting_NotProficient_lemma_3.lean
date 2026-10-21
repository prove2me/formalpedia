-- Prove2me | Theorems.Thm_InterimTesting_NotProficient_lemma_3
-- name    : InterimTesting.NotProficient.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:07.054129+00:00
-- url     : https://prove2.me/theorems/44b4d0d7-bb63-467d-a502-e28aa8dba0e8
-- title:
--   Lemma 3 a), p. 14 (PDF 14) — under (14), for S0 = N, the optimal incentive is 0, 𝒯1(P,0,N), 𝒯1(N,0,N), 𝒯0(N) with budget breakpoints ℋ1, ℋ2, M_U
-- statement:
--   Suppose condition (14) holds and the school starts not proficient. Under the formative assessment, for every budget $M\ge0$ the least optimal merit-based incentive is
--   $$\pi^*=\begin{cases}0,&0\le M<\mathcal H_1(\mu),\\ \mathcal T_1(P,0,N),&\mathcal H_1(\mu)\le M<\mathcal H_2(\mu),\\ \mathcal T_1(N,0,N),&\mathcal H_2(\mu)\le M<\frac{1+(1-\mu)B}{(1-\mu)A}+1,\\ \mathcal T_0(N),&\frac{1+(1-\mu)B}{(1-\mu)A}+1\le M,\end{cases}$$
--   with $\mathcal H_1$ as in (15) and $\mathcal H_2(\mu)=\mu(A+B)(1+(1-\mu)B)\,\mathcal T_1(N,0,N)$ as in (A155). In particular there is a budget level $\mathcal M(N)=\mathcal H_1(\mu)$ below which offering no incentive is optimal.
--
--   **Formalization Note** "Optimal incentive" is `IsOptIncentive` (affordable and attaining the optimal value); the statement is that $\pi^*$ is the least one.
-- source:
--   Virudachalam, Savin & Steinberg, Too Much Information: When Does Additional Testing Benefit Schools?, SSRN 3884543 (version of November 3, 2022), p. 14 (PDF 14), Lemma 3; expanded p. A23 (PDF 49), Lemma 3 a), (A154), (A155), (A162)

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model

namespace InterimTesting.NotProficient

/-- Lemma 3 a), p. 14 (expanded (A162), p. A23): under (14), for `S0 = N` and the formative
assessment, the least optimal incentive is `0` for `M < ℋ1(μ)`, `𝒯1(P, 0, N)` for
`ℋ1(μ) ≤ M < ℋ2(μ)`, `𝒯1(N, 0, N)` for `ℋ2(μ) ≤ M < M_U`, and `𝒯0(N)` for `M ≥ M_U`. -/
theorem lemma_3 (θ : Params) (hθ : θ.Standing) (h14 : Cond14 θ) (M : ℝ) (hM : 0 ≤ M) :
    IsLeast {π | IsOptIncentive θ false .N M π}
      (if M < H1 θ then 0
       else if M < H2 θ then T1 θ false .N 0 .P
       else if M < MU θ then T1 θ false .N 0 .N
       else T0N θ) := by sorry

end InterimTesting.NotProficient
