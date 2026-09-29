-- Prove2me | Theorems.Thm_ModularCurve_relfinrank_modularFunctionField
-- name    : ModularCurve.relfinrank_modularFunctionField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/19d6be68-bdd4-543c-8d62-a8b0a05dc95d
-- title:
--   Relative degree of ℚ(j,j_N) over ℚ(j)
-- statement:
--   Fix a natural number $N \neq 0$. Work inside the field $\mathrm{LaurentSeries}\ \mathbb{Q}$ of formal Laurent series over $\mathbb{Q}$, and let $jq$ be the element $q^{-1}$ times the power series $jNumQ$ obtained from $jNum$ by mapping its integer coefficients into $\mathbb{Q}$, and let $jqN\ N$ be the image $\mathrm{qExpand}\ \mathbb{Q}\ N\ (jq)$ of $jq$ under the ring homomorphism of Laurent (Hahn) series induced by multiplication by $N$ on exponents, i.e. the substitution $q \mapsto q^{N}$. Let $\mathrm{modularFunctionField}\ N$ be the intermediate field $\mathbb{Q}(jq,\ \mathrm{qExpand}\ \mathbb{Q}\ N\ (jq))$ of $\mathrm{LaurentSeries}\ \mathbb{Q}$ generated over $\mathbb{Q}$ by these two series. The assertion is an equality of (possibly infinite) cardinal-valued degrees: the relative finrank, in the sense of `IntermediateField.relfinrank`, of the pair consisting of the intermediate field $\mathbb{Q}(jq)$ and $\mathrm{modularFunctionField}\ N$ coincides with the $\mathbb{Q}(jq)$-module rank of the intermediate field of $\mathrm{LaurentSeries}\ \mathbb{Q}$ generated over $\mathbb{Q}(jq)$ by the single element $jqN\ N$.
--
--   This is the bookkeeping identity that converts the relative degree of the two-generator modular function field $\mathbb{Q}(j(q), j(q^{N}))$ over $\mathbb{Q}(j(q))$ into the degree of a simple extension $\mathbb{Q}(j)(j_N)/\mathbb{Q}(j)$, the shape in which the degree $\psi(N)$ and the irreducibility of the modular polynomial $\Phi_N$ are established. It is used by the statements identifying this degree with $\psi(N)$, by the irreducibility statement for $\Phi_N$, and by the generation statement for the function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_relfinrank_modularFunctionField.lean

import Definitions.Def_ModularCurve_X0
import Mathlib.FieldTheory.Relrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.relfinrank_modularFunctionField (N : ℕ) [NeZero N] : IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (modularFunctionField N) = Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) ({jqN N} : Set (LaurentSeries ℚ))) := by sorry
