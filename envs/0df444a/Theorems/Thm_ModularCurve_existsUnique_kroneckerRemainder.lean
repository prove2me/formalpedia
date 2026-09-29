-- Prove2me | Theorems.Thm_ModularCurve_existsUnique_kroneckerRemainder
-- name    : ModularCurve.existsUnique_kroneckerRemainder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/723c5947-da3c-580f-ada4-329cc414b9a4
-- title:
--   Uniqueness of the Kronecker remainder modulo p
-- statement:
--   Let $p$ be a prime and let $\mathrm{data}$ be a `ModularPolynomialData` for $p$, that is: a polynomial $\Phi \in \mathbb{Z}[X][Y]$ (the outer variable being $Y$, so that `C X` denotes $X$ and `X` denotes $Y$) which is monic in $Y$, whose degree in $Y$ equals $\mathrm{dedekindPsi}\,p = \sum_{d \mid p,\ d \text{ squarefree}} p/d$, and which satisfies $\Phi = 0$ after substituting the $q$-expansion $j(q)$ for $X$ and $j(q^{p})$ for $Y$ in Laurent series over $\mathbb{Q}$. Assume the Kronecker congruence `KroneckerCongruence p data`: the coefficientwise reduction of $\Phi$ along $\mathbb{Z} \to \mathbb{Z}/p$, applied to both layers of coefficients, equals $(X^{p} - Y)(X - Y^{p})$ in $(\mathbb{Z}/p)[X][Y]$. The conclusion is that there is exactly one $R \in \mathbb{Z}[X][Y]$ with $$\Phi = (X^{p} - Y)(X - Y^{p}) + p\,R,$$ the integer $p$ appearing as the doubly constant polynomial `C (C (p : ℤ))`.
--
--   This is the uniqueness and integrality statement attached to Kronecker's congruence for the modular polynomial of prime level: the error term $R$ in $\Phi_p = (X^{p}-Y)(X-Y^{p}) + pR$ is a well-defined element of $\mathbb{Z}[X][Y]$, the "Kronecker remainder". It supplies the canonical datum $(R, h_R)$ used in the analysis of the supersingular crossings of $X_0(p)$ in characteristic $p$, in particular in the local study of the nodes and of the normalised coordinates there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_existsUnique_kroneckerRemainder.lean

import Mathlib
import Definitions.Def_ModularCurve_KroneckerTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial ModularCurve

theorem ModularCurve.existsUnique_kroneckerRemainder (p : ℕ) [Fact p.Prime]
    (data : ModularPolynomialData p) (hK : KroneckerCongruence p data) :
    ∃! R : Polynomial (Polynomial ℤ),
      data.Φ = (C X ^ p - X) * (C X - X ^ p) + C (C (p : ℤ)) * R := by sorry
