-- Prove2me | Theorems.Thm_ModularCurve_exists_variableChange_veluQuotient_toricPoint_tateLaurent_map_qExpand_eq_map_qExpand_mul
-- name    : ModularCurve.exists_variableChange_veluQuotient_toricPoint_tateLaurent_map_qExpand_eq_map_qExpand_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/ae12cd2a-8787-5cba-ba6b-53994211a319
-- title:
--   Vélu quotient of the Tate curve by toric ℓ-torsion
-- statement:
--   Let $K$ be a field of characteristic $0$, let $\ell$ be a prime with $\ell \neq 2$, let $\zeta \in K$ satisfy $\mathrm{IsPrimitiveRoot}\ \zeta\ \ell$, and let $m$ be a nonzero natural number. Write $\mathrm{tateLaurent}\ K$ for the Weierstrass curve over the Laurent series field $\mathrm{LaurentSeries}\ K$ with coefficients $(a_1,a_2,a_3,a_4,a_6) = (1,0,0,\mathrm{tateA4},\mathrm{tateA6})$, obtained from the model over $\mathrm{PowerSeries}\ \mathbb{Z}$ by the ring homomorphism $\mathrm{laurentOfInt}\ K$, and write $\mathrm{qExpand}\ K\ N$ for the injective ring endomorphism of $\mathrm{LaurentSeries}\ K$ multiplying all exponents by $N$ (substitution $q \mapsto q^N$). The assertion is that there is a Weierstrass variable change $C$ over $\mathrm{LaurentSeries}\ K$ whose entries are the constants $u = \ell$, $r = (\ell^2-1)/12$, $s = (\ell-1)/2$, $t = -(\ell^2-1)/24$ (each viewed as a constant Laurent series via `HahnSeries.C`), such that $C$ applied to the Vélu quotient of $(\mathrm{tateLaurent}\ K).\mathrm{map}\ (\mathrm{qExpand}\ K\ m)$ by the finite set $\{\mathrm{toricPoint}\ K\ m\ (\zeta^k) : 1 \le k \le \lfloor \ell/2 \rfloor\}$ equals $(\mathrm{tateLaurent}\ K).\mathrm{map}\ (\mathrm{qExpand}\ K\ (m\ell))$. Here the Vélu quotient of a curve $W$ by a finite set $S$ of pairs keeps $a_1,a_2,a_3$ and replaces $a_4$ by $a_4 - 5\sum_{P \in S} \mathrm{veluT}$, $a_6$ by $a_6 - b_2\sum_{P \in S}\mathrm{veluT} - 7\sum_{P \in S}\mathrm{veluW}$, and $\mathrm{toricPoint}\ K\ p\ c$ is the pair of Laurent series given by the explicit divisor-sum $q$-expansions of the Tate parametrisation coordinates at $u = c$ for the level $p$.
--
--   This is the curve half of the isogeny identity $E_{q^m}/\mu_\ell \cong E_{q^{m\ell}}$ for the Tate curve: Vélu's formulas applied to the half-system of toric $\ell$-torsion points $u = \zeta^k$ produce, after an explicit change of variables with constant coefficients, the Tate model for the parameter $q^{m\ell}$. It feeds the construction of the cyclotomic degeneration data used in the analysis of the modular curve, being cited by [`ModularCurve.variableChange_veluQuotient_tateLaurent_cyclotomicUniv_eq_and_vcXInvR_veluXR_tateToricPoint_eq`](thm.html#ModularCurve.variableChange_veluQuotient_tateLaurent_cyclotomicUniv_eq_and_vcXInvR_veluXR_tateToricPoint_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_variableChange_veluQuotient_toricPoint_tateLaurent_map_qExpand_eq_map_qExpand_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_WeierstrassCurve_Velu

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open WeierstrassCurve

universe u

open scoped Classical in

theorem ModularCurve.exists_variableChange_veluQuotient_toricPoint_tateLaurent_map_qExpand_eq_map_qExpand_mul
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (ζ : K) (hζ : IsPrimitiveRoot ζ ℓ) (m : ℕ) [NeZero m] :
    ∃ C : WeierstrassCurve.VariableChange (LaurentSeries K),
      (C.u : LaurentSeries K) = (ℓ : LaurentSeries K) ∧
        C.r = HahnSeries.C (((ℓ : K) ^ 2 - 1) / 12) ∧
          C.s = HahnSeries.C (((ℓ : K) - 1) / 2) ∧
            C.t = HahnSeries.C (-(((ℓ : K) ^ 2 - 1) / 24)) ∧
              C • ((tateLaurent K).map (qExpand K m)).veluQuotient
                  ((Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K m (ζ ^ k)) =
                (tateLaurent K).map (qExpand K (m * ℓ)) := by sorry
