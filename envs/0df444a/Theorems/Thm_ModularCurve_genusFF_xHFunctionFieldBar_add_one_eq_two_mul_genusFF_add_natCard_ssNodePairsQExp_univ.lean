-- Prove2me | Theorems.Thm_ModularCurve_genusFF_xHFunctionFieldBar_add_one_eq_two_mul_genusFF_add_natCard_ssNodePairsQExp_univ
-- name    : ModularCurve.genusFF_xHFunctionFieldBar_add_one_eq_two_mul_genusFF_add_natCard_ssNodePairsQExp_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/8a5a279b-4210-53c3-ae41-cbaea14b7eb0
-- title:
--   Genus identity for X_H(M) at p ‖ M, arbitrary κ
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number, let $H \le (\mathbb{Z}/M)^{\times}$ be a subgroup, and assume $p \mid M$ but $p^2 \nmid M$, and that every unit of $\mathbb{Z}/M$ whose image under the reduction map $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$ is trivial lies in $H$. Let $\kappa$ be an algebraically closed field of characteristic $p$. Write $\Gamma$ for [`CohCarrier.GammaH`](def/CohCarrier_Level.html#L133) of level $M/p$ and group [`ModularCurve.infSubgroup`](def/ModularCurve_XHDifferentialsModL.html#L246), namely the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of those elements of $\Gamma_0(M/p)$ whose associated unit of $\mathbb{Z}/(M/p)$ lies in the image of $H$ under the reduction map. Then the genus (defined as the $K$-dimension of $H^1$ of the zero divisor, computed through repartitions) of [`ModularCurve.xHFunctionFieldBar M H`](def/ModularCurve_XH.html#L123) — the subfield of $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of the $q$-expansion field of level $\Gamma_H(M)$ over $\mathbb{Q}$ — taken over $\overline{\mathbb{Q}}$, increased by $1$, equals twice the genus over $\kappa$ of the $q$-expansion function field [`ModularCurve.qExpFunctionFieldC κ Γ`](def/ModularCurve_X1.html#L101) plus the number of elements of [`ModularCurve.ssNodePairsQExp κ Γ p`](def/ModularCurve_XHDifferentialsModL.html#L307), the set of pairs $(v,w)$ of places of that function field with $w$ supersingular for $p$ and $v$ the Frobenius place `qExpFrobeniusPlaceModL` of $w$.
--
--   This is the Deligne–Rapoport genus relation between $X_H(M)$ in characteristic zero and the special fibre at an exactly dividing prime $p$, whose two components are copies of $X_{H'}(M/p)$ glued transversally at the supersingular points, in the function-field formulation used by the project. The present form allows the algebraically closed coefficient field $\kappa$ of characteristic $p$ to live in any universe, and feeds the comparison of spaces of weight-two cusp forms with regular differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_genusFF_xHFunctionFieldBar_add_one_eq_two_mul_genusFF_add_natCard_ssNodePairsQExp_univ.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.genusFF_xHFunctionFieldBar_add_one_eq_two_mul_genusFF_add_natCard_ssNodePairsQExp_univ
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (κ : Type*) [Field κ] [CharP κ p] [IsAlgClosed κ] :
    AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) + 1 =
      2 * AlgebraicCurve.genusFF κ ↥(ModularCurve.qExpFunctionFieldC κ (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) +
        Nat.card ↥(ModularCurve.ssNodePairsQExp κ (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) := by sorry
