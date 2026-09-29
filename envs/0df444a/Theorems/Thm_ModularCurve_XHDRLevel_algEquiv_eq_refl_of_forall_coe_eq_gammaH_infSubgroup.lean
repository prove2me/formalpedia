-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_algEquiv_eq_refl_of_forall_coe_eq_gammaH_infSubgroup
-- name    : ModularCurve.XHDRLevel.algEquiv_eq_refl_of_forall_coe_eq_gammaH_infSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/cbe89cec-b220-5cc2-b0ea-a5b4d00e1759
-- title:
--   Rigidity over the level-M/p q-expansion field
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing the kernel of reduction, i.e. such that every unit $u$ of $\mathbb{Z}/M$ with `ZMod.unitsMap` image $1$ in $(\mathbb{Z}/(M/p))^\times$ lies in $H$. Write $F_M :=$ `qExpFunctionFieldC ℚ (ΓM M H)` for the intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$ generated over $\mathbb{Q}$ by all quotients $\mathrm{intSeriesC}\,\mathbb{Q}\,p_f / \mathrm{intSeriesC}\,\mathbb{Q}\,p_g$, where for some weight $k \in \mathbb{Z}$, $f$ and $g$ are modular forms of weight $k$ for the image of the congruence subgroup `ΓM M H` in $\mathrm{GL}_2(\mathbb{R})$, $p_f, p_g \in \mathbb{Z}[[q]]$ are integral $q$-expansions of $f$ and $g$, and the series attached to $p_g$ is nonzero; and let $F_N :=$ `qExpFunctionFieldC ℚ (ΓN p M H hpM)` be the analogous field for the congruence subgroup `ΓN p M H hpM` at level $M/p$. Let $\tau$ be a $\mathbb{Q}$-algebra automorphism of $F_M$ such that $\tau f = f$ whenever $f \in F_M$ and $u \in F_N$ have the same underlying Laurent series. Then $\tau$ is the identity.
--
--   This is the rigidity statement $\operatorname{Aut}_{F(\Gamma')}(F(\Gamma_H(M))) = 1$ for $p \parallel M$, classically a consequence of the self-normalising property of a Borel subgroup of $\mathrm{SL}_2(\mathbb{F}_p)$ acting through the Galois correspondence inside the full level-$M$ field. It is used to pin down uniquely the degeneracy/Atkin–Lehner type chart automorphism of the two-chart model, being cited by [`ModularCurve.XHDRLevel.coe_theta_eq_of_forall_coe_iota0_of_qExpand`](thm.html#ModularCurve.XHDRLevel.coe_theta_eq_of_forall_coe_iota0_of_qExpand) and [`ModularCurve.XHDRLevel.exists_ogg_unit_pair_chartAlgFin_gammaH`](thm.html#ModularCurve.XHDRLevel.exists_ogg_unit_pair_chartAlgFin_gammaH).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_algEquiv_eq_refl_of_forall_coe_eq_gammaH_infSubgroup.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups TensorProduct

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRLevel.algEquiv_eq_refl_of_forall_coe_eq_gammaH_infSubgroup
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (τ : ↥(qExpFunctionFieldC ℚ (ΓM M H)) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    (hτ : ∀ (f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) (u : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))), (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) → τ f = f) :
    τ = AlgEquiv.refl := by sorry
