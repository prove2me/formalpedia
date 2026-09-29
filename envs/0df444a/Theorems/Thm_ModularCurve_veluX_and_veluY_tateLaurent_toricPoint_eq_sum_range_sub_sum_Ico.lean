-- Prove2me | Theorems.Thm_ModularCurve_veluX_and_veluY_tateLaurent_toricPoint_eq_sum_range_sub_sum_Ico
-- name    : ModularCurve.veluX_and_veluY_tateLaurent_toricPoint_eq_sum_range_sub_sum_Ico
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/1b361bf7-6580-5e9f-9d78-16e3dc46e6a7
-- title:
--   Vélu maps at toric points as μ_ℓ-orbit sums
-- statement:
--   Let $K$ be a field of characteristic zero, $\ell$ a prime with $\ell \ne 2$, and $\zeta \in K$ a primitive $\ell$-th root of unity; let $c \in K$ satisfy $c \ne 0$ and $c^{\ell} \ne 1$. Work with `tateLaurent K`, the Weierstrass curve $\langle 1,0,0,a_4,a_6\rangle$ over $\mathrm{LaurentSeries}\,K$ obtained from the Tate coefficients `tateA4`, `tateA6` in $\mathbb{Z}[[q]]$ by coefficientwise base change along $\mathbb{Z} \to K$ followed by the inclusion of power series into Laurent series. For $u \in K$, `toricPoint K 1 u` is the pair of Laurent series whose $x$-component has $q^0$-coefficient $u/(1-u)^2$ and $q^m$-coefficient $\sum_{d \mid m} (m/d)\,(u^{m/d} + u^{-m/d}) - 2\sum_{e \mid m} e$ for $m \ge 1$, and whose $y$-component has $q^0$-coefficient $u^2/(1-u)^3$ and $q^m$-coefficient $\sum_{d \mid m} \bigl(\binom{m/d}{2} u^{m/d} - \binom{m/d+1}{2} u^{-m/d}\bigr) + \sum_{e \mid m} e$. Let $S$ be the image of $\{1,\dots,\lfloor \ell/2 \rfloor\}$ under $k \mapsto$ `toricPoint K 1` $(\zeta^k)$, a finite set of points of the affine plane over $\mathrm{LaurentSeries}\,K$. Then both Vélu expressions $$\mathrm{veluX}_S(x) = x + \sum_{Q \in S}\Bigl(\frac{t_Q}{x - x_Q} + \frac{u_Q}{(x-x_Q)^2}\Bigr),$$ with $g_x = 3x_Q^2 + 2a_2x_Q + a_4 - a_1y_Q$, $g_y = -(2y_Q + a_1x_Q + a_3)$, $t_Q = 2g_x - a_1g_y$, $u_Q = g_y^2$, and its $y$-analogue `veluY`, evaluated at the coordinates of `toricPoint K 1 c`, satisfy $\mathrm{veluX}_S(x(c)) = \sum_{j=0}^{\ell-1} x(c\zeta^j) - \sum_{j=1}^{\ell-1} x(\zeta^j)$ and $\mathrm{veluY}_S(x(c),y(c)) = \sum_{j=0}^{\ell-1} y(c\zeta^j) - \sum_{j=1}^{\ell-1} y(\zeta^j)$, where $x(u), y(u)$ denote the two components of `toricPoint K 1 u`.
--
--   This identifies Vélu's explicit quotient formulae for the subgroup $\mu_\ell$ of the Tate curve, with $S$ a set of representatives of the $\pm$-pairs in $\mu_\ell \setminus \{0\}$, with Vélu's original orbit-sum description $x(P) + \sum_{Q}(x(P+Q) - x(Q))$ read through the toric parametrisation, the group law on toric points being supplied by [`ModularCurve.toricPoint_add_toricPoint_of_charZero`](thm.html#ModularCurve.toricPoint_add_toricPoint_of_charZero). It is used in the comparison of the Vélu quotient of the Tate curve with the Tate curve of parameter $q^\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_veluX_and_veluY_tateLaurent_toricPoint_eq_sum_range_sub_sum_Ico.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_WeierstrassCurve_VeluPointMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve
open ModularCurve

universe u

open scoped Classical in

theorem ModularCurve.veluX_and_veluY_tateLaurent_toricPoint_eq_sum_range_sub_sum_Ico
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (ζ : K) (hζ : IsPrimitiveRoot ζ ℓ) (c : K) (hc0 : c ≠ 0) (hcℓ : c ^ ℓ ≠ 1) :
    (tateLaurent K).veluX ((Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K 1 (ζ ^ k))
        (toricPoint K 1 c).1 =
      ∑ j ∈ Finset.range ℓ, (toricPoint K 1 (c * ζ ^ j)).1 -
        ∑ j ∈ Finset.Ico 1 ℓ, (toricPoint K 1 (ζ ^ j)).1 ∧
    (tateLaurent K).veluY ((Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K 1 (ζ ^ k))
        (toricPoint K 1 c).1 (toricPoint K 1 c).2 =
      ∑ j ∈ Finset.range ℓ, (toricPoint K 1 (c * ζ ^ j)).2 -
        ∑ j ∈ Finset.Ico 1 ℓ, (toricPoint K 1 (ζ ^ j)).2 := by sorry
