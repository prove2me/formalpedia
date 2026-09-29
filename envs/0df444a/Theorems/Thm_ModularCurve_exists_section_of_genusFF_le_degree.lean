-- Prove2me | Theorems.Thm_ModularCurve_exists_section_of_genusFF_le_degree
-- name    : ModularCurve.exists_section_of_genusFF_le_degree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/f018a49b-7acd-5482-8d69-4c2abf3ee930
-- title:
--   Divisors of degree at least the genus admit nonzero sections
-- statement:
--   Let $N$ be a nonzero natural number and let $\bar F_N$ denote `modularFunctionFieldBar N`, the intermediate field of $\overline{\mathbb Q}((q))$ obtained from the field `modularFunctionFieldFull N` — the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by the $q$-expansions `divisorExpansions N` — by adjoining to $\overline{\mathbb Q}$ the image of that subfield under the coefficientwise embedding of $\mathbb Q((q))$ into $\overline{\mathbb Q}((q))$. Here a place of $\bar F_N$ over $\overline{\mathbb Q}$ is a valuation subring of $\bar F_N$ containing the image of $\overline{\mathbb Q}$, distinct from the whole field, and a principal ideal ring; for such a place $v$ and $f \in \bar F_N$, $v.ord f$ is minus the logarithm of the value of $f$ under the associated $\mathbb Z^{m0}$-valued adic valuation, and a divisor is a finitely supported function from places to $\mathbb Z$, its degree being $\sum_v D(v)\,\deg v$. Let $D$ be a divisor and assume that the genus `genusFF`, defined as the $\overline{\mathbb Q}$-dimension of $H^1$ of the zero divisor, is at most $\deg D$ as an integer. Then there is an $f \in \bar F_N$ with $f \neq 0$ and $0 \le D(v) + v.ord f$ for every place $v$.
--
--   This is the standard consequence of Riemann's inequality that a divisor of degree at least the genus has a nonzero Riemann–Roch space, stated here for the function field of $X_0(N)$ over $\overline{\mathbb Q}$ in the unpacked form "there exists a nonzero $f$ with $\operatorname{div}(f) + D \ge 0$". It supplies the auxiliary functions used in the height/mass estimates on $J_0$ and in the comparison of effective divisor classes, being cited by [`ModularCurve.JZero.exists_isRepOf_baseMass_le_heightForm`](thm.html#ModularCurve.JZero.exists_isRepOf_baseMass_le_heightForm), [`ModularCurve.JZero.offBaseMass_le_genusFF_of_riemannRochSpace_eq_bot`](thm.html#ModularCurve.JZero.offBaseMass_le_genusFF_of_riemannRochSpace_eq_bot) and [`ModularCurve.exists_effective_pic0Mk_sub_eq_of_genusFF_le_degree`](thm.html#ModularCurve.exists_effective_pic0Mk_sub_eq_of_genusFF_le_degree).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_section_of_genusFF_le_degree.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_RiemannRochRows

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_section_of_genusFF_le_degree (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ D.degree) :
    ∃ f : modularFunctionFieldBar N, f ≠ 0 ∧
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ D v + v.ord f := by sorry
