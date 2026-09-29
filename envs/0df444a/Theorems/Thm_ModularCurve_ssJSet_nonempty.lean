-- Prove2me | Theorems.Thm_ModularCurve_ssJSet_nonempty
-- name    : ModularCurve.ssJSet_nonempty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/941a7f34-6d06-50f9-aafc-0662782421e4
-- title:
--   Existence of a supersingular j-invariant in characteristic q
-- statement:
--   Let $q$ be a natural number carrying the hypothesis that it is prime, and let $k$ be an algebraically closed field of characteristic $q$ equipped with decidable equality. The set $\mathtt{ssJSet}\ q\ k$ is defined to consist of those $j \in k$ such that for every Weierstrass curve $W$ over $k$ which is elliptic and satisfies $W.j = j$, every point $P$ on the associated affine curve with $q \cdot P = 0$ is the zero point; that is, $j$ is the $j$-invariant only of curves whose group of $k$-points has trivial $q$-torsion. The theorem asserts that this set is nonempty: there exists $j \in k$ with this property. No further hypotheses on $q$ or $k$ are imposed, so the characteristics $q = 2, 3$ are included.
--
--   This is the existence half of Deuring's theorem on supersingular $j$-invariants: over an algebraically closed field of characteristic $q$ there is always at least one supersingular invariant. It feeds the construction of the supersingular locus in the reduction theory of modular curves, and is used at many points downstream in that development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ssJSet_nonempty.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.ssJSet_nonempty {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [DecidableEq k]
    [IsAlgClosed k] [CharP k q] : (ssJSet q k).Nonempty := by sorry
