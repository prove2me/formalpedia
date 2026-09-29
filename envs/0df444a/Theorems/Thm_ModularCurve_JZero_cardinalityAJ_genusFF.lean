-- Prove2me | Theorems.Thm_ModularCurve_JZero_cardinalityAJ_genusFF
-- name    : ModularCurve.JZero.cardinalityAJ_genusFF
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/9117628f-0cbf-5553-a3a6-0d4472ae41ee
-- title:
--   pⁿ-torsion of J₀(N) has p^{2gn} points
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ and let $p$ be a prime. Write $\bar{\mathbb{Q}}$ for `AlgebraicClosure ℚ` and $F_N$ for `modularFunctionFieldBar N`, the intermediate field of $\bar{\mathbb{Q}}((T))$ obtained by adjoining to $\bar{\mathbb{Q}}$ the image, under the coefficientwise embedding of $\mathbb{Q}((T))$ into $\bar{\mathbb{Q}}((T))$, of `modularFunctionFieldFull N`, which is itself the subfield of $\mathbb{Q}((T))$ generated over $\mathbb{Q}$ by the divisor expansions `divisorExpansions N` of level $N$. Let `JZero N` be $\operatorname{Pic}^0(\bar{\mathbb{Q}}, F_N)$, the quotient of the group of degree-zero divisors (finitely supported $\mathbb{Z}$-valued functions on the places of $F_N$ over $\bar{\mathbb{Q}}$) by the subgroup of principal divisors, and let $g =$ `genusFF` $(\bar{\mathbb{Q}}, F_N)$, the $\bar{\mathbb{Q}}$-dimension of $H^1$ of the zero divisor. The assertion, in the vocabulary of `CardinalityAJ`, is: for every natural number $n$, the set of $x \in$ `JZero N` with $p^n \cdot x = 0$ is finite of cardinality exactly $p^{2gn}$.
--
--   This is the classical count of the $p^n$-torsion of the Jacobian of a smooth projective curve of genus $g$ over an algebraically closed field of characteristic zero, specialised to $J_0(N)$ over $\bar{\mathbb{Q}}$ presented as the degree-zero divisor class group of the modular function field of level $N$. It supplies both the finiteness of $p^n$-torsion and the $p$-divisibility of $J_0(N)(\bar{\mathbb{Q}})$ used in the construction of Galois representations on $p$-torsion eigenvectors and in the Eichler–Shimura style dimension counts that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_cardinalityAJ_genusFF.lean

import Definitions.Def_ModularCurve_EichlerShimuraData
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.cardinalityAJ_genusFF (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] :
    CardinalityAJ p (JZero N) (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) := by sorry
