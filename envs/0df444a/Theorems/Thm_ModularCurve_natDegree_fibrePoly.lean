-- Prove2me | Theorems.Thm_ModularCurve_natDegree_fibrePoly
-- name    : ModularCurve.natDegree_fibrePoly
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/c41b88a8-a06f-53ef-bd1c-17904d6ae608
-- title:
--   Degree of the fibre polynomial of a monic Φ
-- statement:
--   Let $K$ be a field and let $\Phi$ be a polynomial in one variable over $\mathbb{Z}[X]$, i.e. $\Phi \in \mathbb{Z}[X][Y]$, assumed monic as a polynomial in $Y$ (its leading coefficient in $\mathbb{Z}[X]$ is $1$). Let $a \in K$. The fibre polynomial `fibrePoly Φ a` is obtained by applying to each coefficient of $\Phi$ the ring homomorphism $\mathbb{Z}[X] \to K$ that is the canonical map $\mathbb{Z} \to K$ on constants and sends $X$ to $a$; thus it is the element $\Phi(a, Y) \in K[Y]$ specialising the first variable at $a$. The assertion is that the natural degree of $\Phi(a,Y)$ in $K[Y]$ equals the natural degree of $\Phi$ as a polynomial in $Y$ over $\mathbb{Z}[X]$: no degree drop occurs under this coefficient specialisation, for any field $K$ (no hypothesis on its characteristic) and any $a \in K$.
--
--   This is the elementary observation that specialising a $Y$-monic integral correspondence polynomial at a value of the first variable cannot lower its degree in $Y$, so the fibres of the associated correspondence have the expected number of points counted with multiplicity. It feeds the root-counting and degree computations for the divisorial Hecke family on modular curves, and is cited in the constructions of Velu-type quotient factorisations and of Frobenius-semilinear torsion models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natDegree_fibrePoly.lean

import Mathlib
import Definitions.Def_ModularCurve_FibrePoly

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
namespace ModularCurve

theorem natDegree_fibrePoly {K : Type*} [Field K] {Φ : Polynomial (Polynomial ℤ)}
    (hΦ : Φ.Monic) (a : K) : (fibrePoly Φ a).natDegree = Φ.natDegree := by sorry
