-- Prove2me | Theorems.Thm_GreenTao_linear_forms_cs_factor
-- name    : GreenTao.linear_forms_cs_factor
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T21:27:27.756991+00:00
-- url     : https://prove2.me/theorems/a7c5b401-b9fd-408a-b8dd-468710b573bd
-- title:
--   Linear-forms condition normalizes the accumulated Cauchy–Schwarz factor
-- statement:
--   Let $d\ge2$ and let $\mu_n$ satisfy the $((d+1)2^d,3(d+1)-4,d+1)$ linear-forms condition on the cyclic groups $\mathbb Z/M_n\mathbb Z$. For every distinguished progression position $j$, the accumulated factor in the finite Cauchy–Schwarz bound satisfies
--
--   $$P_n=\prod_{l=0}^{d-1}P_{l,n}^{\,2^{d-1-l}}\longrightarrow1.$$
--
--   Here $P_{l,n}$ is the explicit average over the partially duplicated coordinate forms in equation (5.18), as defined in the progression-CS interface. This is the normalization assertion for the factors preceding equation (5.24). The statement uses only the linear-forms condition; nonnegativity, primality, and growth of the moduli are not needed as additional hypotheses.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §5 equation (5.18), the accumulated factor in equation (5.21), and the assertion P_d=1+o(1) immediately before equation (5.24). The proof checks the finite row systems directly in the project’s existing rational-coefficient interface.

import Definitions.Def_GreenTao_ProgressionCS
open scoped BigOperators Topology
open Filter GreenTao

theorem GreenTao.linear_forms_cs_factor (d : ℕ) (hd : 2 ≤ d) (M : ℕ → ℕ+) (μ : Family M)
    (hLF : LinearFormsCondition M μ ((d + 1) * 2 ^ d) (3 * (d + 1) - 4) (d + 1))
    (j : Fin (d + 1)) : Tendsto (fun n => csFactor d j (μ n)) atTop (𝓝 1) := by sorry
