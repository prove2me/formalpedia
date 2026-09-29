-- Prove2me | Theorems.Thm_ModularCurve_hasCanonicalDivisor_x1FunctionFieldBar
-- name    : ModularCurve.hasCanonicalDivisor_x1FunctionFieldBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/267e0e58-5909-542c-ad45-e9555b7b51f5
-- title:
--   Existence of canonical divisors on X₁(M) over ℚ̄
-- statement:
--   Let $M$ be a natural number, assumed non-zero. Write $K = \overline{\mathbb{Q}}$ for the algebraic closure of $\mathbb{Q}$ and let $F$ be the field [`ModularCurve.x1FunctionFieldBar M`](def/ModularCurve_X1.html#L182), that is the intermediate field of $K((q)) =$ `LaurentSeries (AlgebraicClosure ℚ)` over $K$ obtained by adjoining to $K$ the image, under the coefficientwise embedding `coeffEmb`, of the $q$-expansion function field `x1FunctionFieldC ℚ M` $\subseteq \mathbb{Q}((q))$ of $X_1(M)$. The conclusion is the class `HasCanonicalDivisor` for the extension $F/K$: for every non-zero Kähler differential $\omega \in \Omega[F\!\restriction\! K]$ there is a divisor $D$, i.e. a finitely supported function from the places of $F/K$ to $\mathbb{Z}$, with $D(v) = v.\mathrm{ordDifferential}\,\omega = v.\mathrm{ord}(v.\mathrm{differentialCoeff}\,\omega)$ for every place $v$. Here a place of $F/K$ is a valuation subring of $F$ that contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. Thus the substance of the assertion is that the function $v \mapsto \mathrm{ord}_v(\omega)$ has finite support, so that $\mathrm{div}(\omega)$ exists as an honest divisor; no statement about its degree being $2g-2$ is made.
--
--   This is the existence of the canonical divisor class for the function field of the modular curve $X_1(M)$ over $\overline{\mathbb{Q}}$, recorded as a typeclass instance so that the Riemann–Roch machinery for divisors applies to this field. It is used in the comparison between the regular differentials of $X_1(M)_{\overline{\mathbb{Q}}}$ and weight-two cusp forms on $\Gamma_1(M)$, [`ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm`](thm.html#ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasCanonicalDivisor_x1FunctionFieldBar.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve

theorem ModularCurve.hasCanonicalDivisor_x1FunctionFieldBar (M : ℕ) [NeZero M] :
    HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.x1FunctionFieldBar M)) := by sorry
