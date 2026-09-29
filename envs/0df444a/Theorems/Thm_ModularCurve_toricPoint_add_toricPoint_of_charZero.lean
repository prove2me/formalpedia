-- Prove2me | Theorems.Thm_ModularCurve_toricPoint_add_toricPoint_of_charZero
-- name    : ModularCurve.toricPoint_add_toricPoint_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/f160c41b-fbe0-5a48-9ee6-4c5cb678eb80
-- title:
--   Toric Tate points add: P_c+P_d=P_{cd} over F((q))
-- statement:
--   Let $F$ be a field of characteristic zero and let $\mathrm{Tate}$ denote `tateLaurent F`, the Weierstrass curve over the Laurent series field $F((q)) =$ `LaurentSeries F` obtained from the curve $y^2 + xy = x^3 + a_4 x + a_6$ over $\mathbb{Z}[[q]]$ with $a_4 =$ `tateA4`, $a_6 =$ `tateA6` (so $a_1 = 1$, $a_2 = a_3 = 0$) by applying the coefficientwise map $\mathbb{Z} \to F$ followed by the inclusion of power series into Hahn series with integer exponents. For $c \in F$ with $c \neq 0$, $c \neq 1$, write $P_c = (X_c, Y_c)$ for `toricPoint F 1 c`, the pair of power series in $F[[q]] \subseteq F((q))$ whose constant terms are $c/(1-c)^2$ and $c^2/(1-c)^3$ and whose $q^m$-coefficients for $m \geq 1$ are $$\sum_{d \mid m} \tfrac{m}{d}\bigl(c^{m/d} + c^{-m/d}\bigr) - 2\sigma_1(m), \qquad \sum_{d \mid m}\Bigl(\binom{m/d}{2} c^{m/d} - \binom{m/d+1}{2} c^{-m/d}\Bigr) + \sigma_1(m)$$ respectively (the case $p = 1$ of `toricPoint`, in which the divisibility conditions are vacuous and $\sigma_1(m) = \sum_{e \mid m} e$). The assertion is: for all such $c$ and $d$ (both nonzero and $\neq 1$), $P_c$ and $P_d$ are nonsingular points of the affine curve $\mathrm{Tate}$, and, as elements of the group $\mathrm{Tate}.\mathrm{Point}$ over $F((q))$, $P_c + P_d = 0$ when $cd = 1$, while if $cd \neq 1$ then $P_{cd}$ is likewise nonsingular and $P_c + P_d = P_{cd}$.
--
--   This is the homomorphism property of Tate's $q$-adic uniformisation $u \mapsto (X(u,q), Y(u,q))$, restricted to constant parameters $u = c \in F^\times \setminus \{1\}$: the map $c \mapsto P_c$ respects multiplication and inversion on the Tate curve over $F((q))$. It is used downstream to produce points of prescribed order on the Tate curve (via primitive roots of unity), to transfer the addition law to the curve `tateBase`, and in the comparison of toric points with $q$-expansion and Vélu-type formulae.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_toricPoint_add_toricPoint_of_charZero.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve WeierstrassCurve WeierstrassCurve.Affine

universe u in

theorem ModularCurve.toricPoint_add_toricPoint_of_charZero
    (F : Type u) [Field F] [CharZero F] [DecidableEq (LaurentSeries F)]
    (c d : F) (hc0 : c ≠ 0) (hd0 : d ≠ 0) (hc1 : c ≠ 1) (hd1 : d ≠ 1) :
    ∃ (hc : (tateLaurent F).toAffine.Nonsingular (toricPoint F 1 c).1 (toricPoint F 1 c).2)
      (hd : (tateLaurent F).toAffine.Nonsingular (toricPoint F 1 d).1 (toricPoint F 1 d).2),
      (c * d = 1 →
        (Point.some (toricPoint F 1 c).1 (toricPoint F 1 c).2 hc : (tateLaurent F).toAffine.Point)
          + Point.some (toricPoint F 1 d).1 (toricPoint F 1 d).2 hd = 0) ∧
      (c * d ≠ 1 →
        ∃ hcd : (tateLaurent F).toAffine.Nonsingular
            (toricPoint F 1 (c * d)).1 (toricPoint F 1 (c * d)).2,
          (Point.some (toricPoint F 1 c).1 (toricPoint F 1 c).2 hc : (tateLaurent F).toAffine.Point)
            + Point.some (toricPoint F 1 d).1 (toricPoint F 1 d).2 hd
            = Point.some (toricPoint F 1 (c * d)).1 (toricPoint F 1 (c * d)).2 hcd) := by sorry
