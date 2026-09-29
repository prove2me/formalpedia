-- Prove2me | Theorems.Thm_ModularCurve_JZero_baseMass_add_single_cuspInftyBar
-- name    : ModularCurve.JZero.baseMass_add_single_cuspInftyBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/34a4e8c3-2a46-585a-9e59-ee69fe1aae57
-- title:
--   The base mass ignores the cusp at infinity
-- statement:
--   Fix $N \ge 1$ (a natural number with `NeZero N`), let $r$ be a natural number and let $s : \mathrm{Fin}\,r \to$ `modularFunctionFieldBar N` be a family of elements of the field obtained by adjoining to $\overline{\mathbb{Q}}$, inside the Laurent series field $\overline{\mathbb{Q}}((q))$, the coefficientwise images of the level-$N$ modular function field `modularFunctionFieldFull N` (itself generated over $\mathbb{Q}$ by the divisor expansions of level $N$). Let $D$ be a divisor on this field over $\overline{\mathbb{Q}}$, i.e. a finitely supported $\mathbb{Z}$-valued function on the places of the project's notion `Place`, and let $m \in \mathbb{Z}$. The assertion is that
--   $$\mathrm{baseMass}_N(s)\bigl(D + m\cdot[\overline{\infty}]\bigr) = \mathrm{baseMass}_N(s)(D),$$
--   where $[\overline{\infty}]$ is `Finsupp.single (cuspInftyBar N) 1`, the cusp place `cuspInftyBar N` being the $q$-adic place $\overline{\infty}$ obtained from the valuation subring of $q$-integral elements together with the witness that the $q$-expansion of $j$ has order $-1$, and where `baseMass N s D` is by definition the finite sum $\sum_{v \neq \overline{\infty}} D_v \cdot \mathrm{baseHt}_s(\overline{\infty}, v)$ over the support of $D$ with the coefficient at $\overline{\infty}$ erased, with $\mathrm{baseHt}_s(b,v) = 0$ for $v = b$ and $\mathrm{baseHt}_s(b,v) = \mathrm{pairHt}_s(v,b)$ otherwise. Thus altering the multiplicity of the cusp in a divisor does not change its base mass.
--
--   This is the padding invariance of the base mass: since the base mass is a sum over the places other than the cusp, adding any integer multiple of the cusp to a divisor leaves it unchanged. It is used when tracking the base mass along the operations on divisor representatives of classes in $J_0(N)$, in [`ModularCurve.JZero.exists_isRepOf_baseMass_le_heightForm`](thm.html#ModularCurve.JZero.exists_isRepOf_baseMass_le_heightForm) and [`ModularCurve.JZero.heightForm_eq_genusFF_mul_baseMass_of_offBaseMass_le_one`](thm.html#ModularCurve.JZero.heightForm_eq_genusFF_mul_baseMass_of_offBaseMass_le_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_baseMass_add_single_cuspInftyBar.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.baseMass_add_single_cuspInftyBar (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (m : ℤ) :
    baseMass N s (D + Finsupp.single (cuspInftyBar N) m) = baseMass N s D := by sorry
