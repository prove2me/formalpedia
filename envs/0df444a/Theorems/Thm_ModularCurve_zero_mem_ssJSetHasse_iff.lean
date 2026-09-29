-- Prove2me | Theorems.Thm_ModularCurve_zero_mem_ssJSetHasse_iff
-- name    : ModularCurve.zero_mem_ssJSetHasse_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/a575558f-83ec-5c8a-b98d-33ad71db7732
-- title:
--   Vanishing Hasse invariant at j=0 iff q≡ 2(mod 3)
-- statement:
--   Let $q$ be a prime with $5 \le q$ and let $K$ be an algebraically closed field of characteristic $q$. For a Weierstrass curve $W$ over a commutative ring, `hasseInvariant q W` denotes the coefficient of $X^{q-1}$ in the $((q-1)/2)$-th power of the polynomial underlying the two-torsion cubic of $W$ (the cubic $4X^3 + b_2X^2 + 2b_4X + b_6$ attached to $W$), and `ssJSetHasse q K` is the set of those $j \in K$ such that every Weierstrass curve $W$ over $K$ which is elliptic (i.e. whose discriminant is a unit) and satisfies $W.j = j$ has `hasseInvariant q W = 0`. The assertion is that $0$ belongs to `ssJSetHasse q K` if and only if $q \bmod 3 = 2$; that is, every elliptic Weierstrass model over $K$ with vanishing $j$-invariant has vanishing Hasse invariant at $q$ exactly when $q \equiv 2 \pmod 3$.
--
--   This is the classical determination of the supersingularity of $j = 0$ in characteristic $q$, in the form of a criterion for the vanishing of the Hasse invariant, and it records one of the two exceptional $j$-invariants in the Hasse-supersingular set. It is used further on in the study of the reduction of modular curves, for instance in counting the Hasse-supersingular $j$-invariants and in the local computations at the supersingular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_zero_mem_ssJSetHasse_iff.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.zero_mem_ssJSetHasse_iff (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (K : Type*) [Field K]
    [IsAlgClosed K] [CharP K q] : (0 : K) ∈ ssJSetHasse q K ↔ q % 3 = 2 := by sorry
