-- Prove2me | Theorems.Thm_ModularCurve_TatePoint_fullKernelDiscAt_univ
-- name    : ModularCurve.TatePoint.fullKernelDiscAt_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/96a55a85-1272-576e-842a-482f190c586a
-- title:
--   Non-vanishing discriminant of the full-kernel Vélu quotient
-- statement:
--   Let $N$ be a natural number, nonzero as a `NeZero` instance, and let $L$ be an algebraically closed field, in an arbitrary universe, with $2 \neq 0$. Let $W$ be a Weierstrass curve over $L$ which is elliptic (its discriminant is a unit), and let $Q$ be a point of the associated affine curve whose exact additive order `addOrderOf Q` equals $N$. Form the finite set of pairs $(x,y) \in L \times L$ obtained as the `coordsOrZero` coordinates of the multiples $k \bullet Q$ for $k = 1, \dots, N-1$ (a `Finset`, so coinciding coordinate pairs are counted once), and set
--   $$t = \sum (3x^2 + 2a_2 x + a_4 - a_1 y), \qquad w = \sum \bigl(x\,(3x^2 + 2a_2 x + a_4 - a_1 y) + y\,(2y + a_1 x + a_3)\bigr),$$
--   the sums over that set, i.e. the sums of `veluGx` and of $x\,$`veluGx`$\,-\,y\,$`veluGy`. Then the Weierstrass curve `W.fullKernelQuotient Q N` with invariants $a_1, a_2, a_3$, $a_4 - 5t$, $a_6 - b_2 t - 7w$ has discriminant $\Delta \neq 0$.
--
--   This is the non-degeneracy clause for the full-kernel form of Vélu's isogeny formulas: the Weierstrass curve produced from $W$ and a point of exact order $N$ by summing the Vélu weights over all nonzero multiples of $Q$ is again non-singular, so it is an elliptic curve. It is used in the construction of the level-$N$ cyclic-subgroup dictionary for modular curves, being cited by [`ModularCurve.exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ`](thm.html#ModularCurve.exists_equiv_ssPlaces_ssLocus_fibre_of_generic_centre_univ) and [`ModularCurve.exists_frobeniusSemilinear_torsionModel_ofJ_univ`](thm.html#ModularCurve.exists_frobeniusSemilinear_torsionModel_ofJ_univ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_TatePoint_fullKernelDiscAt_univ.lean

import Definitions.Def_ModularCurve_CycSubRootBridgeN

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Classical

theorem ModularCurve.TatePoint.fullKernelDiscAt_univ (N : ℕ) [NeZero N] {L : Type*} [Field L] [DecidableEq L]
    [IsAlgClosed L] (h2 : (2 : L) ≠ 0) (W : WeierstrassCurve L) [W.IsElliptic] (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = N) : (W.fullKernelQuotient Q N).Δ ≠ 0 := by sorry
