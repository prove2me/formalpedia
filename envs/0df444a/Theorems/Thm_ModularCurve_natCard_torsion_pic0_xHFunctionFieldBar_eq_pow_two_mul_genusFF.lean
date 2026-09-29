-- Prove2me | Theorems.Thm_ModularCurve_natCard_torsion_pic0_xHFunctionFieldBar_eq_pow_two_mul_genusFF
-- name    : ModularCurve.natCard_torsion_pic0_xHFunctionFieldBar_eq_pow_two_mul_genusFF
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/db81bf56-5b63-5bba-a7e1-1ae3cd144155
-- title:
--   n-torsion of Pic⁰ of X_H(M) has order n^{2g}
-- statement:
--   Let $M$ be a natural number with $M \neq 0$, let $H$ be a subgroup of $(\mathbb{Z}/M)^{\times}$, and let $n$ be a natural number with $n > 0$. Write $F =$ [`ModularCurve.xHFunctionFieldBar M H`](def/ModularCurve_XH.html#L123) for the intermediate field of the Laurent series field $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ obtained by adjoining to $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` the image, under the coefficientwise embedding, of the field [`ModularCurve.xHFunctionFieldC ℚ M H`](def/ModularCurve_XH.html#L76) of $q$-expansions at level $\Gamma_H(M)$; thus $F$ is the base change to $\overline{\mathbb{Q}}$ of the rational function field of $X_H(M)$ in its Laurent-series incarnation. For the pair $\overline{\mathbb{Q}} \subseteq F$, [`AlgebraicCurve.Pic0`](def/AlgebraicCurve_DivisorClassGroup.html#L223) denotes the quotient of the group of degree-zero divisors (finitely supported $\mathbb{Z}$-valued functions on the places of $F$ over $\overline{\mathbb{Q}}$ lying in the kernel of the degree map) by the subgroup of principal divisors, and [`AlgebraicCurve.Pic0.torsion … n`](def/AlgebraicCurve_DivisorClassGroup.html#L244) its subgroup of elements annihilated by $n$. The assertion is that this $n$-torsion subgroup is finite of cardinality exactly $n^{2g}$, where $g =$ [`AlgebraicCurve.genusFF`](def/AlgebraicCurve_Repartitions.html#L145) $(\overline{\mathbb{Q}}, F)$ is the $\overline{\mathbb{Q}}$-dimension of the first repartition cohomology group $H^1(0)$ of the zero divisor.
--
--   This is the classical count of the $n$-torsion of the Jacobian of a curve over an algebraically closed field of characteristic zero, here for the modular curve $X_H(M)$ and phrased in the divisor-class-group currency used throughout the library. It supplies the order of $J_H[n]$ input to the study of the Tate module and of the Néron model of $J_H$ at $p$, and hence to the level-lowering arguments that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_torsion_pic0_xHFunctionFieldBar_eq_pow_two_mul_genusFF.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem ModularCurve.natCard_torsion_pic0_xHFunctionFieldBar_eq_pow_two_mul_genusFF
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (n : ℕ) (hn : 0 < n) :
    Nat.card ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) n) =
      n ^ (2 * AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) := by sorry
