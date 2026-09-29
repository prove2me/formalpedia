-- Prove2me | Theorems.Thm_HenselianLocalRing_existsUnique_isRoot_map_residue_eq_of_isRoot_of_derivative_ne_zero
-- name    : HenselianLocalRing.existsUnique_isRoot_map_residue_eq_of_isRoot_of_derivative_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/4d95c29c-773a-53f1-b44a-216b22845d24
-- title:
--   Unique lifting of simple residual roots over a henselian local ring
-- statement:
--   Let $A_0$ be a commutative ring and $W$ a commutative local ring that is henselian, equipped with an $A_0$-algebra structure. Let $h \in A_0[X]$ be monic, write $g = h$ mapped along $\operatorname{algebraMap} A_0\, W$ for its image in $W[X]$, and let $\bar t$ be an element of the residue field of $W$. Assume that $\bar t$ is a root of the reduction of $g$ modulo the maximal ideal, i.e. the polynomial obtained from $g$ by applying the residue map coefficientwise vanishes at $\bar t$, and that $\bar t$ is not a root of the reduction of the formal derivative $g'$, i.e. the coefficientwise reduction of $\operatorname{derivative} g$ does not vanish at $\bar t$. Then there is exactly one $t \in W$ such that $g(t) = 0$ and the residue of $t$ equals $\bar t$. Note that monicity is stated for $h$ over $A_0$, while the root and simplicity conditions are imposed on the image of $h$ in $W[X]$; the hypothesis that $\bar t$ be simple is phrased as non-vanishing of the reduced derivative rather than as invertibility of $g'(t)$.
--
--   This is the standard uniqueness-with-existence form of Hensel's lemma for henselian local rings: a simple root of the residual polynomial lifts, and lifts uniquely, to a root in the ring. It is used in the construction of integral models of modular curves, where a chart isomorphism is produced by lifting a prescribed residual root of an auxiliary monic polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HenselianLocalRing_existsUnique_isRoot_map_residue_eq_of_isRoot_of_derivative_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing Polynomial

theorem HenselianLocalRing.existsUnique_isRoot_map_residue_eq_of_isRoot_of_derivative_ne_zero
    {A₀ : Type*} [CommRing A₀] (W : Type*) [CommRing W] [Algebra A₀ W] [IsLocalRing W] [HenselianLocalRing W]
    (h : A₀[X]) (hmonic : h.Monic) (tbar : ResidueField W)
    (hroot : ((h.map (algebraMap A₀ W)).map (IsLocalRing.residue W)).IsRoot tbar)
    (hsimple : ¬ ((h.map (algebraMap A₀ W)).derivative.map (IsLocalRing.residue W)).IsRoot tbar) :
    ∃! t : W, (h.map (algebraMap A₀ W)).IsRoot t ∧ IsLocalRing.residue W t = tbar := by sorry
