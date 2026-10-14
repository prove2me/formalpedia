-- Prove2me | Theorems.Thm_IntMul_HvdH_synGad_approx
-- name    : IntMul.HvdH.synGad_approx
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T02:07:17.943086+00:00
-- url     : https://prove2.me/theorems/9ab65dc1-0298-479b-bd5e-a182e0960180
-- title:
--   Multivariate fixed-point FFT over C[y]/(y^r+1) (Proposition 3.3)
-- statement:
--   Let $R=\mathbb C[y]/(y^r+1)$ and $t_i=2^{e_i}$ for $i<d$. Let $\mathcal G_{t_1,\dots,t_d}$ be the normalised multidimensional synthetic transform `synGd` on $\bigotimes_iR^{t_i}$ (`IntMul_HvdH_ConvR`), and $\tilde{\mathcal G}$ its fixed-point version `synGad`. Then $\tilde{\mathcal G}$ approximates $\mathcal G$ at precision $p$ with error
--   $$\varepsilon(\tilde{\mathcal G}_{t_1,\dots,t_d})\le\sum_i\log_2t_i,$$
--   and $\mathcal G$ is $1$-Lipschitz for the sup norm. This is Proposition 3.3 of Harvey–van der Hoeven, which combines Lemma 3.2 with Lemma 2.11.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Proposition 3.3

import Definitions.Def_IntMul_HvdH_ConvR

namespace IntMul.HvdH
theorem synGad_approx {d : ℕ} (p r : ℕ) (e : Fin d → ℕ) :
    FPApprox p (synGad r e) (synGd r e) (∑ i, (e i : ℝ)) ∧ SupLip (synGd r e) := by sorry
end IntMul.HvdH
