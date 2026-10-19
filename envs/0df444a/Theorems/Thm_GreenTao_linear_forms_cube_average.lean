-- Prove2me | Theorems.Thm_GreenTao_linear_forms_cube_average
-- name    : GreenTao.linear_forms_cube_average
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T21:16:15.607979+00:00
-- url     : https://prove2.me/theorems/5ed0f6bd-2bfd-4f52-858c-07dc398041f7
-- title:
--   Linear-forms condition normalizes Gowers cube averages
-- statement:
--   Let $\nu_n$ satisfy the $(m_0,t_0,L_0)$ linear-forms condition. For $d\ge0$, assume $2^d\le m_0$, $d+1\le t_0$, and $1\le L_0$. Then
--
--   $$C_d(\nu_n)=\mathbb E_{x,h_1,\ldots,h_d}\prod_{\omega\in\{0,1\}^d}\nu_n(x+\omega\cdot h)\longrightarrow1.$$
--
--   This is the unweighted cube-moment input in the generalized von Neumann argument. It uses only the linear-forms condition; no primality, correlation condition, or nonnegativity is needed beyond that condition as formally stated.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §5, observation immediately before Lemma 5.2, and Lemma 5.5, q=0 case; §5 Definition 5.1, equations (5.1)/(5.4). The d=0 case is also included and gives normalization of the mean.

import Definitions.Def_GreenTao_Uniformity
open scoped BigOperators Topology
open Filter GreenTao

theorem GreenTao.linear_forms_cube_average (M : ℕ → ℕ+) (ν : GreenTao.Family M) (m₀ t₀ L₀ d : ℕ)
    (hν : GreenTao.LinearFormsCondition M ν m₀ t₀ L₀)
    (hm : 2 ^ d ≤ m₀) (ht : d + 1 ≤ t₀) (hL₀ : 1 ≤ L₀) :
    Tendsto (fun n => GreenTao.cubeAvg d (ν n)) atTop (𝓝 1) := by sorry
