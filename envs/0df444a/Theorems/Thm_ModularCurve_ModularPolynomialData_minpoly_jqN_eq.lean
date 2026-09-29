-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_minpoly_jqN_eq
-- name    : ModularCurve.ModularPolynomialData.minpoly_jqN_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/b0379d9b-b1fe-5675-80fe-28b986ad2036
-- title:
--   Irreducible Φ_N is the minimal polynomial of j(q^N)
-- statement:
--   Let $N$ be a positive natural number. Work inside the field $\mathbb{Q}((q))$ of Laurent series over $\mathbb{Q}$ (in Lean, `LaurentSeries ℚ`), with $j$ represented by [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), the Laurent series $q^{-1}$ times the power series obtained from the integral numerator series `jNum` by base change to $\mathbb{Q}$, and with [`ModularCurve.jqN N`](def/ModularCurve_X0.html#L194) the image of `jq` under the ring homomorphism `qExpand ℚ N`, which multiplies all exponents by $N$, i.e. the substitution $q \mapsto q^{N}$. Let `data` be a term of [`ModularCurve.ModularPolynomialData N`](def/ModularCurve_X0.html#L215), that is: a polynomial $\Phi \in (\mathbb{Z}[X])[Y]$ which is monic in $Y$, has $Y$-degree equal to $\sum_{d \mid N,\ d\ \text{squarefree}} N/d$ (the Dedekind $\psi$-function), and satisfies $\Phi(j, j(q^{N})) = 0$ in $\mathbb{Q}((q))$, where the coefficients in $\mathbb{Z}[X]$ are evaluated at $X =$ `jq`. Write `data.toAdjoin` for the polynomial in $\mathbb{Q}\langle j\rangle[Y]$ obtained from $\Phi$ by applying, coefficientwise, the ring homomorphism $\mathbb{Z}[X] \to \mathbb{Q}\langle j \rangle$ sending $X$ to the canonical generator of the intermediate field $\mathbb{Q}\langle j\rangle =$ `ℚ⟮jq⟯` of $\mathbb{Q}((q))$. Assume `PhiIrreducible data`, namely that `data.toAdjoin` is irreducible in $\mathbb{Q}\langle j\rangle[Y]$. Then the minimal polynomial of `jqN N` over $\mathbb{Q}\langle j \rangle$ equals `data.toAdjoin`.
--
--   This identifies the classical modular polynomial $\Phi_N(j, Y)$ as the minimal polynomial of $j(q^{N})$ over $\mathbb{Q}(j)$, once irreducibility is known. It is used for the uniqueness of the modular polynomial data at prime level and in the divisibility statement relating products of such data to a resultant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_minpoly_jqN_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve IntermediateField

theorem ModularCurve.ModularPolynomialData.minpoly_jqN_eq {N : ℕ} [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) (hirr : ModularCurve.PhiIrreducible data) :
    minpoly (↥ℚ⟮ModularCurve.jq⟯) (ModularCurve.jqN N) = data.toAdjoin := by sorry
