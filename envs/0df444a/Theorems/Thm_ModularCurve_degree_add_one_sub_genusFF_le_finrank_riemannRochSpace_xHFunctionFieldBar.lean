-- Prove2me | Theorems.Thm_ModularCurve_degree_add_one_sub_genusFF_le_finrank_riemannRochSpace_xHFunctionFieldBar
-- name    : ModularCurve.degree_add_one_sub_genusFF_le_finrank_riemannRochSpace_xHFunctionFieldBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/cfd60fb4-ff96-52de-abd0-437a435547a2
-- title:
--   Riemann's inequality for X_H(M) over ℚ̄
-- statement:
--   Let $M$ be a non-zero natural number, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$, and let $F =$ `xHFunctionFieldBar M H` be the intermediate field of $\overline{\mathbb{Q}} \subseteq \overline{\mathbb{Q}}((q))$ obtained as `laurentBaseChange`, i.e. generated over $\overline{\mathbb{Q}}$ by the coefficientwise image under `coeffEmb` of the $q$-expansion function field `xHFunctionField M H` $=$ `xHFunctionFieldC ℚ M H` attached to level $M$ and $H$ inside $\mathbb{Q}((q))$. Let $D$ be a divisor of $F$ over $\overline{\mathbb{Q}}$, that is, a finitely supported $\mathbb{Z}$-valued function on the set of places of $F/\overline{\mathbb{Q}}$, a place being a valuation subring of $F$ containing the image of $\overline{\mathbb{Q}}$, distinct from $F$ itself, and a principal ideal ring. Then $$\deg D + 1 - g \le \dim_{\overline{\mathbb{Q}}} L(D),$$ an inequality of integers, where $\deg D = \sum_v D(v)\,\deg v$, where $g =$ `genusFF` is the $\overline{\mathbb{Q}}$-dimension of the repartition cohomology group $H^1$ of the zero divisor, and where $L(D) =$ `riemannRochSpace D` is the $\overline{\mathbb{Q}}$-subspace of those $f \in F$ with $v(f) \le \exp(D(v))$ for every place $v$, the valuation being the adic valuation of $v$ with values in $\mathbb{Z}^{m0}$.
--
--   This is Riemann's inequality for the function field of the modular curve $X_H(M)$ over $\overline{\mathbb{Q}}$, stated with the repartition (adelic) genus and the Riemann–Roch space of a divisor. It supplies the existence of functions with prescribed poles used in the construction of models and prolongation data for places of $X_H(M)$, and is cited by the results on common units with prescribed poles and on elements of Riemann–Roch spaces with prescribed residues and Galois behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_degree_add_one_sub_genusFF_le_finrank_riemannRochSpace_xHFunctionFieldBar.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RiemannRochRows

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.degree_add_one_sub_genusFF_le_finrank_riemannRochSpace_xHFunctionFieldBar
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    D.degree + 1 - (genusFF (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) : ℤ)
      ≤ (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace D) : ℤ) := by sorry
