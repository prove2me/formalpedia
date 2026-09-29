-- Prove2me | Theorems.Thm_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot
-- name    : ModularCurve.exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/6397dd98-954e-5d69-a123-9d4cc38d4d1c
-- title:
--   Toric point of exact order M on the Tate curve
-- statement:
--   Let $K$ be a field, let $M \ge 2$ be a natural number and let $\zeta \in K$ be a primitive $M$-th root of unity; let $L$ be a field equipped with an algebra structure over the field $K((q))$ of formal Laurent series over $K$ (Hahn series with integer exponents). Write $E$ for the base change to $L$ of the Tate curve `tateLaurent K`, that is, of the Weierstrass curve over $K((q))$ with $a_1 = 1$, $a_2 = a_3 = 0$ and $a_4, a_6$ the images of Tate's integral power series `tateA4`, `tateA6` under reduction of coefficients to $K$ followed by the inclusion of power series into Laurent series. For $c \in K$, `toricPoint K 1 c` denotes the pair of power series in $q$ whose first entry has constant term $c/(1-c)^2$ and $m$-th coefficient $\sum_{d \mid m} d\,(c^{d} + c^{-d}) - 2\sigma_1(m)$, and whose second entry has constant term $c^2/(1-c)^3$ and $m$-th coefficient $\sum_{d \mid m}\bigl(\binom{d}{2}c^{d} - \binom{d+1}{2}c^{-d}\bigr) + \sigma_1(m)$. The assertion is that there is a point $P$ of the group of affine points of $E$ such that, for every natural number $n$, $n \cdot P = 0$ holds precisely when $M \mid n$, and such that for every natural number $n$ with $M \nmid n$ the images in $L$ of the two entries of `toricPoint K 1 (ζ ^ n)` are the coordinates of a nonsingular point of $E$ and $n \cdot P$ is that affine point.
--
--   This is Tate's uniformisation $u \mapsto (X(u,q), Y(u,q))$ restricted to the group $\mu_M(K)$ of $M$-th roots of unity, in purely formal form: the toric point with parameter $\zeta$ has exact order $M$ and its multiples are the toric points with parameters $\zeta^n$. It supplies the canonical order-$M$ point used to put level structures on the Tate curve, and is cited by the results on $q$-expansions and classification of points of modular curves at full level, at $\Gamma_1$ and at $\Gamma_H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve WeierstrassCurve WeierstrassCurve.Affine

universe u v in

theorem ModularCurve.exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot
    (K : Type u) [Field K] (M : ℕ) (hM : 2 ≤ M) (ζ : K) (hζ : IsPrimitiveRoot ζ M)
    (L : Type v) [Field L] [DecidableEq L] [Algebra (LaurentSeries K) L] :
    ∃ P : ((tateLaurent K).baseChange L).toAffine.Point,
      (∀ n : ℕ, n • P = 0 ↔ M ∣ n) ∧
      ∀ n : ℕ, ¬ M ∣ n →
        ∃ h : ((tateLaurent K).baseChange L).toAffine.Nonsingular
            (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).1)
            (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).2),
          n • P = WeierstrassCurve.Affine.Point.some
            (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).1)
            (algebraMap (LaurentSeries K) L (toricPoint K 1 (ζ ^ n)).2) h := by sorry
