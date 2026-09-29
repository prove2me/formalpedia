-- Prove2me | Theorems.Thm_ModularCurve_unitsMap_div_eq_one_imp_mem_unitsMap_ker_mul
-- name    : ModularCurve.unitsMap_div_eq_one_imp_mem_unitsMap_ker_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/e1176a9d-db7e-5a28-94ac-29bcc786dffc
-- title:
--   Triviality modulo M₀q/q gives membership in the kernel
-- statement:
--   Let $q$ and $M_0$ be natural numbers, with $q$ assumed prime (as a `Fact` instance) and $M_0$ assumed nonzero (as a `NeZero` instance), and let $hpM$ be a proof that $q$ divides $M_0 q$. Write $M = M_0 q$, so that $M/q$ divides $M$ by `Nat.div_dvd_of_dvd hpM`, and $M_0$ divides $M$ by `dvd_mul_right M₀ q`; each divisibility gives a reduction homomorphism on unit groups via `ZMod.unitsMap`. The assertion is: for every unit $u \in (\mathbb{Z}/M_0q)^\times$ whose image under the reduction map $(\mathbb{Z}/M_0q)^\times \to (\mathbb{Z}/((M_0q)/q))^\times$ is $1$, the unit $u$ lies in the kernel of the reduction map $(\mathbb{Z}/M_0q)^\times \to (\mathbb{Z}/M_0)^\times$. Thus the only mathematical content beyond the identity $(M_0q)/q = M_0$ is the transport of the hypothesis along that equality of natural numbers, including the change of the divisibility proof indexing the reduction map.
--
--   This is the bookkeeping step identifying the two descriptions of the level-lowering reduction map at $q$ on unit groups: the subgroup condition $H \supseteq \ker\big((\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/q))^\times\big)$ required by the $\Gamma_H(M)$ model data at $p = q$ is matched with the kernel of reduction to level $M_0$, where $M = M_0q$. It is used in [`ModularCurve.pic0_x1x0FunctionFieldC_smul_smul_sub_self_eq_of_mem_inertiaSubgroupIn`](thm.html#ModularCurve.pic0_x1x0FunctionFieldC_smul_smul_sub_self_eq_of_mem_inertiaSubgroupIn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_unitsMap_div_eq_one_imp_mem_unitsMap_ker_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.unitsMap_div_eq_one_imp_mem_unitsMap_ker_mul (q M₀ : ℕ) [Fact q.Prime] [NeZero M₀]
    (hpM : q ∣ M₀ * q) (u : (ZMod (M₀ * q))ˣ) (hu : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1) :
    u ∈ (ZMod.unitsMap (dvd_mul_right M₀ q)).ker := by sorry
