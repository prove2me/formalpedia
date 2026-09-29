-- Prove2me | Theorems.Thm_ModularCurve_JZero_eq_single_add_single_cuspInftyBar_of_offBaseMass_le_one
-- name    : ModularCurve.JZero.eq_single_add_single_cuspInftyBar_of_offBaseMass_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/aee92cb2-94d1-5841-adaa-6befb235267c
-- title:
--   Effective divisors of off-cusp mass at most one
-- statement:
--   Let $N \ge 1$ and write $F = \overline{\mathbb{Q}} \cdot \mathrm{modularFunctionFieldFull}(N)$ for the base change `modularFunctionFieldBar N`, i.e. the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise images of the functions in the field `modularFunctionFieldFull N` $\subseteq \mathbb{Q}((q))$. A divisor is a finitely supported function $D$ from the places of $F$ over $\overline{\mathbb{Q}}$ (valuation subrings of $F$ containing $\overline{\mathbb{Q}}$, proper, and principal ideal rings) to $\mathbb{Z}$, and `cuspInftyBar N` is the $q$-adic place at infinity, obtained from the subring of elements of nonnegative $q$-order, the hypothesis for its construction being witnessed by the $q$-expansion of $j$, of order $-1$. Assume $D$ is effective, $0 \le D(v)$ for every place $v$, and that its off-cusp mass $\sum_{v \ne \infty} D(v)$ — the sum of the coefficients of $D$ after erasing the coefficient at `cuspInftyBar N` — is at most $1$. Then, setting $k = D(\infty)$, either $D = k \cdot \infty$, or there is a place $v \ne \infty$ with $D = 1\cdot v + k \cdot \infty$.
--
--   An elementary classification of the effective divisors on the base-changed modular curve of level $N$ that carry at most one point of multiplicity off the cusp at infinity: they are multiples of the cusp, possibly plus a single further place with coefficient one. It isolates the degenerate configurations of a divisor representing a point of $J_0(N)$, and is used by [`ModularCurve.JZero.exists_isRepOf_baseMass_le_heightForm`](thm.html#ModularCurve.JZero.exists_isRepOf_baseMass_le_heightForm) and [`ModularCurve.JZero.heightForm_eq_genusFF_mul_baseMass_of_offBaseMass_le_one`](thm.html#ModularCurve.JZero.heightForm_eq_genusFF_mul_baseMass_of_offBaseMass_le_one), where the height form is evaluated directly in these cases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_eq_single_add_single_cuspInftyBar_of_offBaseMass_le_one.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.eq_single_add_single_cuspInftyBar_of_offBaseMass_le_one (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hD : ∀ v, 0 ≤ D v)
    (hm : offBaseMass N D ≤ 1) :
    D = Finsupp.single (cuspInftyBar N) (D (cuspInftyBar N)) ∨
      ∃ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v ≠ cuspInftyBar N ∧
        D = Finsupp.single v 1 + Finsupp.single (cuspInftyBar N) (D (cuspInftyBar N)) := by sorry
