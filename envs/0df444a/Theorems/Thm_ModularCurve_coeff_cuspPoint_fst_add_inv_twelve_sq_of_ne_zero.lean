-- Prove2me | Theorems.Thm_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq_of_ne_zero
-- name    : ModularCurve.coeff_cuspPoint_fst_add_inv_twelve_sq_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/199f46ba-6bd6-5ce2-b58f-9eeb1f1053cf
-- title:
--   Non-toric Tate cusp: coefficients of (xᵥ+tfrac112)²
-- statement:
--   Let $L$ be a field of characteristic zero, let $N$ be a nonzero natural number, let $\xi$ be a unit of $L$ whose image in $L$ is a primitive $N$-th root of unity, and let $v : \mathrm{Fin}\,2 \to \mathbb{Z}/N$ satisfy $v \neq 0$ and $v_1 \neq 0$ (the first condition being implied by the second). Since $v_1 \neq 0$, the point [`ModularCurve.cuspPoint L N ξ v`](def/ModularCurve_KatzLevelPCusps.html#L59) is by definition [`ModularCurve.nonToricPoint L N (ξ ^ (v 0).val) ((v 1).val)`](def/ModularCurve_TateSlots.html#L35), whose first component $x_v$ is the Laurent series over $L$ obtained from the power series `slotSubst L N (ξ ^ (v 0).val) ((v 1).val) ModularCurve.tateUnivX` by the inclusion of power series into Laurent series. The assertion is that for every natural number $n \ge 1$ the coefficient of the Laurent series $(x_v + \mathrm{C}(12^{-1}))^2$ in degree $n \in \mathbb{Z}$ equals
--   $$\tfrac16 \sum_{(m,d)\,:\,md=n} d^{3}\Bigl(\mathbf{1}[\,m \equiv v_1 \ (\mathrm{mod}\ N)\,]\,\xi^{\,d\,(v_0)_{\mathrm{val}}} + \mathbf{1}[\,m \equiv -v_1 \ (\mathrm{mod}\ N)\,]\,\xi^{-d\,(v_0)_{\mathrm{val}}}\Bigr) + \mathbf{1}[\,N \mid n\,]\,\tfrac{240}{144}\sum_{d \mid (n/N)} d^{3},$$
--   the first sum being over the pairs in `Nat.divisorsAntidiagonal n`, the residues $m \bmod N$ being the images of the natural numbers $m$ in $\mathbb{Z}/N$, and the powers of $\xi$ and $\xi^{-1}$ being taken in $L^\times$ and then mapped into $L$.
--
--   This is the $q$-expansion form, at a non-toric torsion point $\xi^{v_0}q^{v_1}$ on the Tate curve with parameter $q^N$, of the Weierstrass relation $\wp^2 = \wp''/6 + E_4/144$ for the shifted abscissa; the divisor-sum shape of the right-hand side is the Eisenstein series attached to the line $v_1 i + (N-v_1)k = n$ together with the diagonal contribution $\sigma_3(n/N)$. It is the $v_1 \neq 0$ half of [`ModularCurve.coeff_cuspPoint_fst_add_inv_twelve_sq`](thm.html#ModularCurve.coeff_cuspPoint_fst_add_inv_twelve_sq), and the proof goes through the universal Tate identity [`ModularCurve.sub_one_mul_coeff_tateUnivX_eq`](thm.html#ModularCurve.sub_one_mul_coeff_tateUnivX_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq_of_ne_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.coeff_cuspPoint_fst_add_inv_twelve_sq_of_ne_zero
    (L : Type) [Field L] [CharZero L] (N : ℕ) [NeZero N] (ξ : Lˣ) (hξ : IsPrimitiveRoot (ξ : L) N)
    (v : Fin 2 → ZMod N) (hv : v ≠ 0) (hv1 : v 1 ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    (((ModularCurve.cuspPoint L N ξ v).1 + HahnSeries.C ((12 : L)⁻¹)) ^ 2).coeff (n : ℤ) =
      (6 : L)⁻¹ * ∑ md ∈ Nat.divisorsAntidiagonal n,
          ((md.2 : ℕ) : L) ^ 3 *
            ((if ((md.1 : ℕ) : ZMod N) = v 1 then ((ξ ^ (md.2 * (v 0).val) : Lˣ) : L) else 0) +
              (if ((md.1 : ℕ) : ZMod N) = -v 1 then ((ξ⁻¹ ^ (md.2 * (v 0).val) : Lˣ) : L) else 0)) +
        (if N ∣ n then (240 / 144 : L) * ((Nat.divisors (n / N)).sum fun d => ((d : ℕ) : L) ^ 3) else 0) := by sorry
