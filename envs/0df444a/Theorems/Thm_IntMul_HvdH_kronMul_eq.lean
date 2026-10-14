-- Prove2me | Theorems.Thm_IntMul_HvdH_kronMul_eq
-- name    : IntMul.HvdH.kronMul_eq
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T22:50:15.677487+00:00
-- url     : https://prove2.me/theorems/87deee14-3187-4c1b-8911-701dae08aaee
-- title:
--   Polynomial multiplication by Kronecker substitution is exact
-- statement:
--   Let $p\ge0$ and $1\le r$ with $2r<2^p$, and let $a,b$ be integer coefficient lists of length $r$ with all entries bounded by $2^p$ in absolute value. Then multiplying the integers $a(2^{3p})$ and $b(2^{3p})$ and reading off $2r-1$ balanced base-$2^{3p}$ digits gives exactly the coefficients of the product $ab\in\mathbb Z[y]$.
--   This is steps (1)–(3) of Lemma 2.5 of Harvey–van der Hoeven (see `IntMul_HvdH_KronMul`).
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemma 2.5 (Kronecker substitution)

import Definitions.Def_IntMul_HvdH_KronMul

namespace IntMul.HvdH
theorem kronMul_eq (p r : ℕ) (a b : List ℤ) (ha : a.length = r) (hb : b.length = r)
    (hab : ∀ x ∈ a, |x| ≤ 2 ^ p) (hbb : ∀ x ∈ b, |x| ≤ 2 ^ p) (hr : 1 ≤ r) (hrp : 2 * r < 2 ^ p) :
    kronMul p r a b = polyMul a b := by sorry
end IntMul.HvdH
