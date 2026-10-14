-- Prove2me | Theorems.Thm_IntMul_HvdH_mulR_eq_spec
-- name    : IntMul.HvdH.mulR_eq_spec
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T22:49:21.660677+00:00
-- url     : https://prove2.me/theorems/c623a351-a6b5-4cd1-a838-f70cfa218934
-- title:
--   Fixed-point multiplication in $\mathbb C[y]/(y^r+1)$ via Kronecker substitution (Lemma 2.5)
-- statement:
--   Let $p\ge0$ and $1\le r$ with $2r<2^p$, and let $U_0,U_1,V_0,V_1$ be integer coefficient lists of length $r$ with entries bounded by $2^p$ in absolute value (so $u=2^{-p}(U_0+iU_1)$ and $v=2^{-p}(V_0+iV_1)$ are fixed-point elements of $\mathbb C[y]/(y^r+1)$). The algorithm `mulR` computes the four products $U_jV_k$ by Kronecker substitution, reduces modulo $y^r+1$ and rounds. Its output equals the specification `mulRSpec`, i.e. the exact coefficients of $2^{2p}r\cdot uv/r$ divided by $2^pr$ and rounded towards zero.
--   This is the correctness part of Lemma 2.5 of Harvey–van der Hoeven (see `IntMul_HvdH_KronMul`).
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemma 2.5 (Kronecker substitution)

import Definitions.Def_IntMul_HvdH_KronMul

namespace IntMul.HvdH
theorem mulR_eq_spec (p r : ℕ) (U0 U1 V0 V1 : List ℤ)
    (h0 : U0.length = r) (h1 : U1.length = r) (h2 : V0.length = r) (h3 : V1.length = r)
    (hU0 : ∀ x ∈ U0, |x| ≤ 2 ^ p) (hU1 : ∀ x ∈ U1, |x| ≤ 2 ^ p)
    (hV0 : ∀ x ∈ V0, |x| ≤ 2 ^ p) (hV1 : ∀ x ∈ V1, |x| ≤ 2 ^ p) (hr : 1 ≤ r)
    (hrp : 2 * r < 2 ^ p) :
    mulR p r U0 U1 V0 V1 = mulRSpec p r U0 U1 V0 V1 := by sorry
end IntMul.HvdH
