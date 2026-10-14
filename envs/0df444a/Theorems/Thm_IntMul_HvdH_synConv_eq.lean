-- Prove2me | Theorems.Thm_IntMul_HvdH_synConv_eq
-- name    : IntMul.HvdH.synConv_eq
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T02:07:32.078552+00:00
-- url     : https://prove2.me/theorems/0b743b99-28f5-4a4c-8db3-855402cd7690
-- title:
--   Convolution over C[y]/(y^r+1) via synthetic transforms
-- statement:
--   Let $R=\mathbb C[y]/(y^r+1)$ and $t_i=2^{e_i}$ with $2\le t_i\mid 2r$ for $i<d$. Put $T=r\prod_it_i$. For $u,v\in\bigotimes_iR^{t_i}$, the normalised convolution is computed by synthetic transforms:
--   $$\frac Tr\,\mathcal G^*\Bigl(\tfrac1r\,(\mathcal Gu)\cdot(\mathcal Gv)\Bigr)=\frac1T\,u*v,$$
--   where $\mathcal G=$ `synGd`, $\mathcal G^*=$ `synGdInv`, the product $\cdot$ is pointwise multiplication in $R$, and $*$ is the convolution `convR` (cyclic in each $R$-axis, negacyclic in $y$). The identity holds at every in-range index. This is the identity (2.1) used in the proof of Proposition 3.4 of Harvey–van der Hoeven.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, (2.1) and proof of Proposition 3.4

import Definitions.Def_IntMul_HvdH_ConvR

namespace IntMul.HvdH
theorem synConv_eq (r : ℕ) (hr : 0 < r) {d : ℕ} (e : Fin d → ℕ) (he1 : ∀ i, 1 ≤ e i)
    (he : ∀ i, 2 ^ e i ∣ 2 * r) (u v : (Fin (d + 1) → ℕ) → ℂ) (j : Fin (d + 1) → ℕ)
    (hj : ∀ i : Fin d, j i.castSucc < 2 ^ e i) (hc : j (Fin.last d) < r) :
    (2 ^ (∑ i, e i) : ℂ) * synGdInv r e (mulPt r (synGd r e u) (synGd r e v)) j =
      convR r e u v j := by sorry
end IntMul.HvdH
