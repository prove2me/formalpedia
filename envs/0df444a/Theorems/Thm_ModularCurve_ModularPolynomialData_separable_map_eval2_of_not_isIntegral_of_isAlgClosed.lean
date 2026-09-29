-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_eval2_of_not_isIntegral_of_isAlgClosed
-- name    : ModularCurve.ModularPolynomialData.separable_map_eval2_of_not_isIntegral_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/f5d3041f-cda8-5d2b-8cb4-c32a105be34a
-- title:
--   Separability of Φₚ(j₀,Y) for non-integral j₀
-- statement:
--   Let $F$ be an algebraically closed field of characteristic zero and let $p$ be a prime. Let `data` be a modular polynomial datum of level $p$: a polynomial $\Phi \in (\mathbb{Z}[X])[Y]$ which is monic in $Y$, whose degree in $Y$ equals $\psi(p) = \sum_{d \mid p,\ d \text{ squarefree}} p/d$ (the Dedekind $\psi$-value, here $p+1$), and which vanishes when its coefficients in $\mathbb{Z}[X]$ are specialised through `evalAtJ`, the ring map $\mathbb{Z}[X] \to$ Laurent series over $\mathbb{Q}$ sending $X$ to the $q$-expansion of $j$, and $Y$ is given the value of the corresponding expansion at level $p$. Let $jv \in F$ be an element that is not integral over $\mathbb{Z}$. Then the polynomial in $F[Y]$ obtained from $\Phi$ by applying, coefficientwise, the ring homomorphism $\mathbb{Z}[X] \to F$ which reduces integers into $F$ and evaluates $X$ at $jv$, is separable, i.e. coprime to its derivative.
--
--   This is the classical assertion that the modular equation $\Phi_p(j_0, Y)$ has $p+1$ distinct roots whenever $j_0$ is not an algebraic integer, the mechanism being that such a $j_0$ forces the endomorphism ring of a curve with invariant $j_0$ to be $\mathbb{Z}$, so that the $p+1$ cyclic subgroups of order $p$ yield pairwise non-isomorphic quotients. It is the algebraically closed, characteristic-zero case used by [`ModularCurve.ModularPolynomialData.separable_map_eval2_of_not_isIntegral`](thm.html#ModularCurve.ModularPolynomialData.separable_map_eval2_of_not_isIntegral).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_separable_map_eval2_of_not_isIntegral_of_isAlgClosed.lean

import Definitions.Def_ModularCurve_X0
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial ModularCurve

theorem ModularCurve.ModularPolynomialData.separable_map_eval2_of_not_isIntegral_of_isAlgClosed
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime]
    (data : ModularPolynomialData p) (jv : F) (hjv : ¬ _root_.IsIntegral ℤ jv) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) jv)).Separable := by sorry
