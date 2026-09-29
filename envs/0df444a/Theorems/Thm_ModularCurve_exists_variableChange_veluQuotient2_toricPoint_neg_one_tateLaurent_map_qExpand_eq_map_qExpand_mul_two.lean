-- Prove2me | Theorems.Thm_ModularCurve_exists_variableChange_veluQuotient2_toricPoint_neg_one_tateLaurent_map_qExpand_eq_map_qExpand_mul_two
-- name    : ModularCurve.exists_variableChange_veluQuotient2_toricPoint_neg_one_tateLaurent_map_qExpand_eq_map_qExpand_mul_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/bea2905f-b7c4-51c9-9816-fbae21dce732
-- title:
--   Vélu 2-quotient of the Tate curve of q^m is that of q^{2m}
-- statement:
--   Let $K$ be a field of characteristic $0$ and let $m$ be a nonzero natural number. Write $E$ for `tateLaurent K`, the Weierstrass curve over $K((q))$ with $a_1 = 1$, $a_2 = a_3 = 0$ and $a_4, a_6$ the images of the integral Tate coefficients `tateA4`, `tateA6` under the map sending a power series over $\mathbb{Z}$ to a Laurent series over $K$, and write $E^{(m)}$ for its base change along `qExpand K m`, the ring endomorphism of $K((q))$ multiplying all exponents by $m$ (that is, $q \mapsto q^m$). Let $(x_0, y_0) =$ `toricPoint K m (-1)`, the pair of Laurent series whose $n$-th coefficients are, for $c = -1$ and $n > 0$, $\sum_{d \mid n,\ m \mid d} (n/d)\bigl(c^{n/d} + c^{-n/d}\bigr) - 2\,[m \mid n]\,\sigma_1(n/m)$ and $\sum_{d \mid n,\ m \mid d}\bigl(\binom{n/d}{2} c^{n/d} - \binom{n/d+1}{2} c^{-n/d}\bigr) + [m \mid n]\,\sigma_1(n/m)$, with constant terms $c/(1-c)^2$ and $c^2/(1-c)^3$. Then there exists a Weierstrass variable change $C$ over $K((q))$ whose unit $u$ has value $2$ and whose $r, s, t$ are the constant series $1/4$, $1/2$, $-1/8$, such that applying $C$ to the order-two Vélu quotient of $E^{(m)}$ at $(x_0, y_0)$ — the curve with the same $a_1, a_2, a_3$, with $a_4$ replaced by $a_4 - 5g$ and $a_6$ by $a_6 - b_2 g - 7 x_0 g$, where $g = 3x_0^2 + 2a_2 x_0 + a_4 - a_1 y_0$ — gives exactly $E$ base changed along `qExpand K (m * 2)`.
--
--   This is the even-prime case of the statement that Vélu's quotient of the Tate curve of $q^m$ by the subgroup $\mu_2$ of the toric part is the Tate curve of $q^{2m}$, the isogeny being $u \mapsto u^2$ on $\mathbb{G}_m/q^{m\mathbb{Z}}$; the transformation constants are the values at $\ell = 2$ of $(\ell, (\ell^2-1)/12, (\ell-1)/2, -(\ell^2-1)/24)$. It serves as the prime-$2$ step in the induction identifying the quotients of the Tate curve by cyclic subgroups of the toric part, and is used in [`ModularCurve.variableChange_veluQuotient2_tateLaurent_cyclotomicUniv_eq_and_vcXInvR_velu2XR_tateToricPoint_eq`](thm.html#ModularCurve.variableChange_veluQuotient2_tateLaurent_cyclotomicUniv_eq_and_vcXInvR_velu2XR_tateToricPoint_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_variableChange_veluQuotient2_toricPoint_neg_one_tateLaurent_map_qExpand_eq_map_qExpand_mul_two.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_WeierstrassCurve_VeluOrderTwo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve

universe u

theorem ModularCurve.exists_variableChange_veluQuotient2_toricPoint_neg_one_tateLaurent_map_qExpand_eq_map_qExpand_mul_two
    (K : Type u) [Field K] [CharZero K] (m : ℕ) [NeZero m] :
    ∃ C : WeierstrassCurve.VariableChange (LaurentSeries K),
      (C.u : LaurentSeries K) = (2 : LaurentSeries K) ∧
        C.r = HahnSeries.C ((1 : K) / 4) ∧
          C.s = HahnSeries.C ((1 : K) / 2) ∧
            C.t = HahnSeries.C (-((1 : K) / 8)) ∧
              C • ((tateLaurent K).map (qExpand K m)).veluQuotient2 (toricPoint K m (-1)).1 (toricPoint K m (-1)).2 =
                (tateLaurent K).map (qExpand K (m * 2)) := by sorry
