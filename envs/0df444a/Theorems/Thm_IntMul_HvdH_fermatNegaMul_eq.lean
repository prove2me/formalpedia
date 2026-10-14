-- Prove2me | Theorems.Thm_IntMul_HvdH_fermatNegaMul_eq
-- name    : IntMul.HvdH.fermatNegaMul_eq
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T04:11:20.344795+00:00
-- url     : https://prove2.me/theorems/4a0b9d7e-4e88-4f04-9c9b-cb8c02f52b20
-- title:
--   Exact negacyclic multiplication through a Fermat-type modulus
-- statement:
--   Let $n,P\ge1$ and let $u,v\in\mathbb Z^n$ have entries of absolute value at most $M$, where $4nM^2<2^P$. Put $B=2^P$ and $F=B^n+1$. The algorithm `fermatNegaMul` evaluates $u,v$ at $y=B$ (so $y^n\equiv-1\pmod F$). It reduces both values modulo $F$, multiplies them modulo $F$, takes the balanced residue in $(-F/2,F/2]$, and reads off $n$ balanced base-$B$ digits. It returns exactly the coefficients of the product in $\mathbb Z[y]/(y^n+1)$:
--   $$w_k=\sum_{i\le k}u_iv_{k-i}-\sum_{k<i<n}u_iv_{k+n-i}\qquad(0\le k<n).$$
--   So a negacyclic polynomial product costs one multiplication modulo the Fermat-type number $2^{nP}+1$. This replaces the Kronecker step of Lemma 2.5 of Harvey–van der Hoeven when the pointwise products are done exactly.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemma 2.5 (variant)

import Definitions.Def_IntMul_HvdH_Fermat

namespace IntMul.HvdH
theorem fermatNegaMul_eq (P n : ℕ) (u v : List ℤ) (M : ℤ) (hn : 1 ≤ n) (hP1 : 1 ≤ P)
    (hu : u.length = n) (hv : v.length = n) (hM0 : 0 ≤ M)
    (hub : ∀ x ∈ u, |x| ≤ M) (hvb : ∀ x ∈ v, |x| ≤ M) (hP : 4 * n * M ^ 2 < 2 ^ P) :
    fermatNegaMul P n u v = negFold n (polyMul u v) := by sorry
end IntMul.HvdH
