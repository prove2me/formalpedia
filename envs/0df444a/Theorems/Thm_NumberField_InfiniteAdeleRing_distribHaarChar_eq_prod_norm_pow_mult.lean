-- Prove2me | Theorems.Thm_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult
-- name    : NumberField.InfiniteAdeleRing.distribHaarChar_eq_prod_norm_pow_mult
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/9be78985-c4db-5390-b2c6-49f255dbb04e
-- title:
--   Modulus of a unit acting on the infinite adele ring
-- statement:
--   Let $K$ be a number field, and equip its infinite adele ring $K_\infty = \prod_{w \mid \infty} K_w$ (the product of the completions of $K$ at its infinite places) with a measurable space structure that is the Borel structure of its topology. Let $a$ be a unit of the ring $K_\infty$. Then the value at $a$ of Mathlib's `distribHaarChar` for the additive group $K_\infty$ with its multiplicative action of units — the nonnegative real scaling factor $\delta(a)$ characterised by $\mu(a \cdot S) = \delta(a)\,\mu(S)$ for an additive Haar measure $\mu$ on $K_\infty$ — is, as a real number, equal to $$\prod_{w \mid \infty} \lVert a_w \rVert^{m_w},$$ the product being over all infinite places $w$ of $K$, where $a_w$ is the component at $w$ of the underlying element of $K_\infty$, $\lVert \cdot \rVert$ is the norm of the completion $K_w$, and $m_w$ is `InfinitePlace.mult`, namely $1$ if $w$ is real and $2$ if $w$ is complex.
--
--   This is the archimedean case of the standard computation of the module of an idele (Weil, Tate), here in the form of the distributive Haar character of the unit group of $K_\infty$ acting on $K_\infty$. It supplies the Jacobian factors for changes of variable $x \mapsto ax$ in integrals over $K_\infty$, and is used in the archimedean orbital-integral computations for $\mathrm{GL}_2$ in the automorphic part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

theorem NumberField.InfiniteAdeleRing.distribHaarChar_eq_prod_norm_pow_mult
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    (a : (InfiniteAdeleRing K)ˣ) :
    (distribHaarChar (InfiniteAdeleRing K) a : ℝ) = ∏ w : InfinitePlace K, ‖(a : InfiniteAdeleRing K) w‖ ^ w.mult := by sorry
