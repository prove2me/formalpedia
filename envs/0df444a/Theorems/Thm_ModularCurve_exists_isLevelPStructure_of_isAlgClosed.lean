-- Prove2me | Theorems.Thm_ModularCurve_exists_isLevelPStructure_of_isAlgClosed
-- name    : ModularCurve.exists_isLevelPStructure_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/d633a871-3272-53b7-8654-fb04ce2dc7a9
-- title:
--   Level-p structures exist over algebraically closed fields
-- statement:
--   Let $K$ be an algebraically closed field, let $W$ be a Weierstrass curve over $K$ given by coefficients $a_1,a_2,a_3,a_4,a_6$, and let $p$ be a prime with $p \neq 2$, with $p \neq 0$ in $K$, and suppose the discriminant $\Delta(W)$ is nonzero. Then there exists a quadruple $D = (x_P, y_P, x_Q, y_Q)$ of elements of $K$ (a [`ModularCurve.LevelPData K`](def/ModularCurve_KatzLevelP.html#L43)) satisfying [`ModularCurve.IsLevelPStructure W p D`](def/ModularCurve_KatzLevelP.html#L104), i.e. all of the following: both $(x_P,y_P)$ and $(x_Q,y_Q)$ satisfy the affine Weierstrass equation of $W$; the polynomial $\mathrm{pre}\Psi_p$ of $W$ vanishes at $x_P$ and at $x_Q$; and the two elements
--   $$\iota_p(x_P,x_Q) = \prod_{a=1}^{(p-1)/2}\bigl(x_Q\,\Psi^2_a(x_P) - \Phi_a(x_P)\bigr), \qquad \iota_p(x_Q,x_P) = \prod_{a=1}^{(p-1)/2}\bigl(x_P\,\Psi^2_a(x_Q) - \Phi_a(x_Q)\bigr)$$
--   are units in $K$, i.e. nonzero. Thus $W$ carries a level-$p$ structure expressed purely in division-polynomial coordinates: two affine $p$-torsion points whose $x$-coordinates are mutually independent in the sense measured by $\iota_p$.
--
--   This is the non-emptiness of the geometric fibres of the scheme of level-$p$ bases attached to a Weierstrass curve, in the division-polynomial presentation of Katz–Mazur; classically it records that $W[p](K) \cong (\mathbb{Z}/p)^2$ admits a basis when $p$ is invertible and $W$ is nonsingular. It feeds the flatness and faithful flatness statements for the level-$p$ basis ring, and a classification of $\Gamma_0$-type data at full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isLevelPStructure_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ModularCurve.exists_isLevelPStructure_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] (W : WeierstrassCurve K) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) (hΔ : W.Δ ≠ 0) :
    ∃ D : ModularCurve.LevelPData K, ModularCurve.IsLevelPStructure W p D := by sorry
