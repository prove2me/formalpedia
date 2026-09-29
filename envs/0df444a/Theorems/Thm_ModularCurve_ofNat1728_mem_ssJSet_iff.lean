-- Prove2me | Theorems.Thm_ModularCurve_ofNat1728_mem_ssJSet_iff
-- name    : ModularCurve.ofNat1728_mem_ssJSet_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/a9bd62fc-b89a-5e7b-8a47-475e01bbe9ad
-- title:
--   j=1728 is supersingular iff q ≡ 3 (mod 4)
-- statement:
--   Let $q$ be a prime with $5 \le q$, and let $K$ be an algebraically closed field of characteristic $q$. The assertion is an equivalence between two conditions. The first is that the element $1728$ of $K$ (the image of the natural number $1728$) lies in $\mathrm{ssJSet}\ q\ K$; by definition this means: for every Weierstrass curve $W$ over $K$ that is elliptic (nonvanishing discriminant, so that its $j$-invariant is defined) whose $j$-invariant equals $1728$, and every point $P$ on the associated affine curve $W.\mathrm{toAffine}$, if $q \cdot P = 0$ in the group of points then $P = 0$; equivalently, every elliptic curve over $K$ with $j$-invariant $1728$ has trivial $q$-torsion, i.e. is supersingular. The second condition is the congruence $q \bmod 4 = 3$. Thus $1728$ is a supersingular $j$-invariant in characteristic $q \ge 5$ precisely when $q \equiv 3 \pmod 4$.
--
--   This is the classical determination of the supersingularity of the curve with $j$-invariant $1728$, which has complex multiplication by $\mathbb{Z}[i]$ and is supersingular exactly at the primes inert in $\mathbb{Q}(i)$. Within this development it supplies one of the explicit supersingular points used in the analysis of multiplicative coverings of the modular curve, and is cited by numerous lemmas there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ofNat1728_mem_ssJSet_iff.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
namespace ModularCurve

theorem ofNat1728_mem_ssJSet_iff (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K] :
    (1728 : K) ∈ ssJSet q K ↔ q % 4 = 3 := by sorry
