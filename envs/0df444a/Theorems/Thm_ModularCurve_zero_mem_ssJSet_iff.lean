-- Prove2me | Theorems.Thm_ModularCurve_zero_mem_ssJSet_iff
-- name    : ModularCurve.zero_mem_ssJSet_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/393935c9-aa50-5e58-9555-309a66ee2a4f
-- title:
--   j=0 is supersingular in characteristic q≥ 5 iff q≡ 2(mod 3)
-- statement:
--   Let $q$ be a prime with $5 \le q$, and let $K$ be an algebraically closed field of characteristic $q$. The assertion is an equivalence: $0$ belongs to the set $\mathrm{ssJSet}\,q\,K$ if and only if $q \equiv 2 \pmod 3$. Here $\mathrm{ssJSet}\,q\,K$ is, by definition, the set of those $j \in K$ such that for every Weierstrass curve $W$ over $K$ which is elliptic (nonvanishing discriminant) and satisfies $W.j = j$, every point $P$ of the associated affine curve with $q \cdot P = 0$ is the zero point. Thus the conclusion says: every elliptic curve over $K$ with $j$-invariant $0$ has trivial $q$-torsion group of $K$-points — equivalently, is supersingular — precisely when $q$ is congruent to $2$ modulo $3$. Note that the condition defining membership is a statement about all Weierstrass models with the given $j$-invariant, and that no individual curve is singled out.
--
--   This is the classical determination of when $j=0$ is a supersingular invariant: the curve $y^2 = x^3 + 1$ has complex multiplication by $\mathbb{Z}[\zeta_3]$ and is supersingular exactly at the primes inert in $\mathbb{Q}(\sqrt{-3})$. Together with the companion statement at $j = 1728$ and the mass formula it controls the set of supersingular $j$-invariants in characteristic $q$, and it is used in the analysis of multiplicative coverings and Hasse-exponent data on modular curves in this development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_zero_mem_ssJSet_iff.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
namespace ModularCurve

theorem zero_mem_ssJSet_iff (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K] :
    (0 : K) ∈ ssJSet q K ↔ q % 3 = 2 := by sorry
