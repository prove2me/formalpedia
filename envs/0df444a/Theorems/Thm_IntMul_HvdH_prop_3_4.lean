-- Prove2me | Theorems.Thm_IntMul_HvdH_prop_3_4
-- name    : IntMul.HvdH.prop_3_4
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T02:08:24.470994+00:00
-- url     : https://prove2.me/theorems/b4d13258-3e7e-4c80-952d-6e5927d82d71
-- title:
--   Fixed-point convolution over C[y]/(y^r+1) (Proposition 3.4)
-- statement:
--   Let $R=\mathbb C[y]/(y^r+1)$ and $t_i=2^{e_i}$ with $2\le t_i\mid2r$ for $i<d$. Put $K=\sum_ie_i$, so that $T/r=2^K$. Assume $2r<2^p$. For fixed-point arrays $U,V$ in the unit polydisc, the algorithm $\tilde{\mathcal M}_R=$ `convRa` returns an array in the polydisc. At every in-range index it satisfies
--   $$\bigl|\tilde{\mathcal M}_R(U,V)-2^p\,\mathcal M_R(2^{-p}U,2^{-p}V)\bigr|\le 2^K(6K+3)+3,$$
--   where $\mathcal M_R(u,v)=\tfrac1Tu*v$ is the exact normalised convolution `convR`. Since $r\ge2$, this is at most the bound $3T\log_2T+2T+3$ of Proposition 3.4 of Harvey–van der Hoeven.
--
--   The algorithm is: forward fixed-point synthetic transforms, pointwise products by Kronecker substitution (Lemma 2.5), the inverse transform, and scaling by $2^K$ (Lemma 2.2).
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Proposition 3.4

import Definitions.Def_IntMul_HvdH_ConvR

namespace IntMul.HvdH
theorem prop_3_4 {d : ℕ} (p r : ℕ) (e : Fin d → ℕ) (hr : 1 ≤ r) (hrp : 2 * r < 2 ^ p)
    (he1 : ∀ i, 1 ≤ e i) (he : ∀ i, 2 ^ e i ∣ 2 * r)
    (U V : (Fin (d + 1) → ℕ) → ℤ × ℤ) (hU : InDisc p U) (hV : InDisc p V) :
    InDisc p (convRa p r e U V) ∧
      ∀ j : Fin (d + 1) → ℕ, (∀ i : Fin d, j i.castSucc < 2 ^ e i) → j (Fin.last d) < r →
        ‖gC (convRa p r e U V j) - 2 ^ p *
          convR r e (fun x => gC (U x) / 2 ^ p) (fun x => gC (V x) / 2 ^ p) j‖ ≤
          2 ^ (∑ i, e i) * (6 * (∑ i, e i) + 3) + 3 := by sorry
end IntMul.HvdH
