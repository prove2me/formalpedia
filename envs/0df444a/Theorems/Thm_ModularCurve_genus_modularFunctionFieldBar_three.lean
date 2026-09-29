-- Prove2me | Theorems.Thm_ModularCurve_genus_modularFunctionFieldBar_three
-- name    : ModularCurve.genus_modularFunctionFieldBar_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/896bdfe8-db65-5e8e-b395-420e209ab6cb
-- title:
--   The level-3 modular function field over ℚ̄ has genus 0
-- statement:
--   Let $K=\overline{\mathbb{Q}}$ be the algebraic closure of $\mathbb{Q}$ and let $F$ be the subfield [`ModularCurve.modularFunctionFieldBar 3`](def/ModularCurve_ArithmeticGalois.html#L111) of the Laurent series field $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$, namely the intermediate field obtained by adjoining to $\overline{\mathbb{Q}}$ the image, under the coefficientwise embedding $\mathrm{LaurentSeries}(\mathbb{Q}) \to \mathrm{LaurentSeries}(\overline{\mathbb{Q}})$, of the field [`ModularCurve.modularFunctionFieldFull 3`](def/ModularCurve_X0.html#L305) $= \mathbb{Q}(\text{divisorExpansions } 3)$ generated over $\mathbb{Q}$ by the divisor expansions of level $3$. Assume the extension $\overline{\mathbb{Q}} \subseteq F$ satisfies [`AlgebraicCurve.HasCanonicalDivisor`](def/AlgebraicCurve_CanonicalDivisor.html#L14): for every nonzero Kähler differential $\omega \in \Omega[F/\overline{\mathbb{Q}}]$ there is a divisor $D$, i.e. a finitely supported $\mathbb{Z}$-valued function on the places of $F$ over $\overline{\mathbb{Q}}$ (valuation subrings of $F$ containing the image of $\overline{\mathbb{Q}}$, distinct from $F$ itself, and principal ideal rings), with $D(v) = v.\mathrm{ordDifferential}(\omega)$ at every place $v$, the order at $v$ of the differential coefficient of $\omega$. Then the natural number [`AlgebraicCurve.genus`](def/AlgebraicCurve_CanonicalDivisor.html#L33) of this extension — defined, when a nonzero differential exists, as $(\deg D + 2)^{+}/2$ for the chosen canonical divisor $D$, and as $0$ otherwise — equals $0$.
--
--   This is the assertion that the modular curve $X_0(3)$ over $\overline{\mathbb{Q}}$ has genus zero, in the function-field formulation used throughout the treatment of modular curves here. It is used to show that the degree-zero divisor class group $J_0(3)$ of this field is trivial ([`ModularCurve.subsingleton_jZero_three`](thm.html#ModularCurve.subsingleton_jZero_three)), and thence to dispose of the case $q = 3$ in statements about $X_0(q)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_genus_modularFunctionFieldBar_three.lean

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.genus_modularFunctionFieldBar_three
    [AlgebraicCurve.HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.modularFunctionFieldBar 3))] :
    AlgebraicCurve.genus (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar 3) = 0 := by sorry
