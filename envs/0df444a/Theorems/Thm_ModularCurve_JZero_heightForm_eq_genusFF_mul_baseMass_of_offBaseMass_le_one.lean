-- Prove2me | Theorems.Thm_ModularCurve_JZero_heightForm_eq_genusFF_mul_baseMass_of_offBaseMass_le_one
-- name    : ModularCurve.JZero.heightForm_eq_genusFF_mul_baseMass_of_offBaseMass_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/170a4d0a-fd19-5be3-97ba-dd7a564b0cb9
-- title:
--   Height form equals genus times base mass when off-cusp mass ≤ 1
-- statement:
--   Fix $N \ge 1$ and let $\bar F =$ `modularFunctionFieldBar N`, the intermediate field of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise images of the field $\mathbb Q(\mathrm{divisorExpansions}\,N)$, and let $g =$ `genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N)`, the $\overline{\mathbb Q}$-dimension of $H^1(0)$. Let $r \in \mathbb N$ and let $s : \mathrm{Fin}\,r \to \bar F$ be any finite family of elements of $\bar F$ (no spanning or basis hypothesis), and let $D$ be a divisor, i.e. a finitely supported $\mathbb Z$-valued function on the places of $\bar F$ over $\overline{\mathbb Q}$ in the sense of `Place` (valuation subrings of $\bar F$ containing $\overline{\mathbb Q}$, proper, with principal ideal ring structure). Assume $D$ is effective, $D(v) \ge 0$ for every place $v$, and that its mass away from the cusp $b =$ `cuspInftyBar N` satisfies $\mathrm{offBaseMass}(D) = \sum_{v \neq b} D(v) \le 1$. Write $t(v) = \mathrm{baseHt}\,s\,b\,v$, equal to $0$ for $v = b$ and to `pairHt s v b` otherwise. The conclusion is that the quadratic height form at $D$, namely the value of `heightFormAux` on $D$ with the coefficient at $b$ erased, with genus parameter $g$ and base point $b$, $$\Bigl(g + \sum_{v \neq b} D(v) - 1\Bigr)\sum_{v \neq b} D(v)t(v) - \tfrac12 \sum_{\substack{v,w \in \mathrm{supp}(D \setminus b) \\ v \neq w}} D(v)D(w)\,\mathrm{pairHt}\,s\,v\,w - (2 - 2g)\sum_{v \neq b} \frac{D(v)(D(v)-1)}{2}\,t(v),$$ equals $g \cdot \mathrm{baseMass}(D) = g\sum_{v \neq b} D(v)\,t(v)$.
--
--   This is the degenerate case of the comparison between the quadratic height form on divisors representing points of $J_0(N)$ and the base-height-weighted mass: when an effective divisor carries at most one point outside the cusp at infinity, the height form is exactly $g$ times the mass, with no error term. It is used in [`ModularCurve.JZero.exists_isRepOf_baseMass_le_heightForm`](thm.html#ModularCurve.JZero.exists_isRepOf_baseMass_le_heightForm), where the remaining, genuinely quadratic, many-point case is treated separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_heightForm_eq_genusFF_mul_baseMass_of_offBaseMass_le_one.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.heightForm_eq_genusFF_mul_baseMass_of_offBaseMass_le_one (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hD : ∀ v, 0 ≤ D v)
    (hm : offBaseMass N D ≤ 1) :
    heightForm N s D = (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) * baseMass N s D := by sorry
