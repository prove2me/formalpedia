-- Prove2me | Theorems.Thm_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq
-- name    : ModularCurve.coeff_cuspPoint_fst_add_inv_twelve_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/07c5130f-afd1-5063-b0db-2a40f0c21b8c
-- title:
--   Divisor-sum coefficients of (xᵥ+1/12)² at Tate cusp points
-- statement:
--   Let $L$ be a field of characteristic zero, $N$ a nonzero natural number, $\xi \in L^\times$ a unit whose image in $L$ is a primitive $N$-th root of unity, and $v : \mathrm{Fin}\,2 \to \mathbb{Z}/N$ a nonzero pair, so $v = (v_0, v_1)$. Write $x_v \in L((q))$ for the first component of [`ModularCurve.cuspPoint L N ξ v`](def/ModularCurve_KatzLevelPCusps.html#L59), that is: for $v_1 = 0$ the power series over $L$ whose $m$-th coefficient, for $m \neq 0$, is $\sum_{d \mid m,\ N \mid d} (m/d)\bigl(c^{m/d} + c^{-m/d}\bigr) - 2\,[N \mid m]\,\sigma_1(m/N)$ with $c = \xi^{(v_0).\mathrm{val}}$ and constant term $c(1-c)^{-2}$; and for $v_1 \neq 0$ the series $\mathrm{ofPowerSeries}$ of `slotSubst L N c (v 1).val tateUnivX` with the same $c$. Then for every natural $n \geq 1$ the coefficient of index $n$ of $(x_v + \mathrm{C}(12^{-1}))^2$ equals
--   $$6^{-1} \sum_{md = n} d^3 \Bigl( [\,m \equiv v_1 \ (N)\,]\,\xi^{d\,(v_0).\mathrm{val}} + [\,m \equiv -v_1 \ (N)\,]\,\xi^{-d\,(v_0).\mathrm{val}} \Bigr) + [\,N \mid n\,]\,\tfrac{240}{144} \sum_{d \mid n/N} d^3,$$
--   the first sum being over ordered factorisations $(m,d)$ of $n$ into naturals. Nothing is asserted about the coefficients of index $\leq 0$.
--
--   This is the $q$-expansion form of the Weierstrass relation $\wp^2 = \wp''/6 + g_2/12$, evaluated at the $N$-torsion point of the Tate curve indexed by $v$: the positive-index coefficients of $(x_v + 1/12)^2$ are those of a weight-four level-$N$ Eisenstein series, written as divisor sums. It feeds the construction of the weight-four modular forms attached to Tate torsion points, used in [`ModularCurve.FullLevel.AuxLevel.exists_modularForm_weight_four_qExpansion_eq_cuspPoint_sq_and_cFour`](thm.html#ModularCurve.FullLevel.AuxLevel.exists_modularForm_weight_four_qExpansion_eq_cuspPoint_sq_and_cFour) and its $\Gamma_H$-level counterpart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.coeff_cuspPoint_fst_add_inv_twelve_sq
    (L : Type) [Field L] [CharZero L] (N : ℕ) [NeZero N] (ξ : Lˣ) (hξ : IsPrimitiveRoot (ξ : L) N)
    (v : Fin 2 → ZMod N) (hv : v ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    (((ModularCurve.cuspPoint L N ξ v).1 + HahnSeries.C ((12 : L)⁻¹)) ^ 2).coeff (n : ℤ) =
      (6 : L)⁻¹ * ∑ md ∈ Nat.divisorsAntidiagonal n,
          ((md.2 : ℕ) : L) ^ 3 *
            ((if ((md.1 : ℕ) : ZMod N) = v 1 then ((ξ ^ (md.2 * (v 0).val) : Lˣ) : L) else 0) +
              (if ((md.1 : ℕ) : ZMod N) = -v 1 then ((ξ⁻¹ ^ (md.2 * (v 0).val) : Lˣ) : L) else 0)) +
        (if N ∣ n then (240 / 144 : L) * ((Nat.divisors (n / N)).sum fun d => ((d : ℕ) : L) ^ 3) else 0) := by sorry
