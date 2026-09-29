-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_index_levelH_inf_ker_unitsMap_eq_and_neg_one_notMem
-- name    : ModularCurve.FullLevel.index_levelH_inf_ker_unitsMap_eq_and_neg_one_notMem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/7e426c7d-3178-597c-a0ad-4ac7883574f7
-- title:
--   Index of H₁ in (ℤ/q²M')^×, and -1notin H₁
-- statement:
--   Let $q$ be a prime, let $M'$ be a non-zero natural number coprime to $q$, and let $\ell_g$ be a prime with $\ell_g \ge 3$ dividing $M'$. Let $H_1$ be a subgroup of $(\mathbb{Z}/q^2M')^\times$ which is assumed equal to the intersection of [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22) — by definition the kernel of the reduction map $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$ induced by $q \mid q^2M'$ — with the kernel of the reduction map $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell_g)^\times$ induced by $\ell_g \mid q^2 \cdot M'$. The conclusion is the conjunction of two assertions: the index of $H_1$ in $(\mathbb{Z}/q^2M')^\times$ equals $\varphi(q)\,(\ell_g - 1)$, where $\varphi$ is Euler's totient, and the unit $-1$ of $\mathbb{Z}/q^2M'$ does not lie in $H_1$.
--
--   This is the elementary index and sign computation for the multiplicative level group cut out by the congruence conditions "trivial modulo $q$ and modulo $\ell_g$" inside $(\mathbb{Z}/q^2M')^\times$, i.e. for the group attached to the level structure $\Gamma(q)\cap\Gamma_0(M')\cap\Gamma_1(\ell_g)$. It feeds the orbit count [`ModularCurve.FullLevel.Diamond.two_mul_index_gammaH_sup_zpowers_neg_one_le_ncard_orbit_gamma1`](thm.html#ModularCurve.FullLevel.Diamond.two_mul_index_gammaH_sup_zpowers_neg_one_le_ncard_orbit_gamma1), where both the value of the index and the failure of $-1$ to belong to the group are needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_index_levelH_inf_ker_unitsMap_eq_and_neg_one_notMem.lean

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.index_levelH_inf_ker_unitsMap_eq_and_neg_one_notMem
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hcop : Nat.Coprime q M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg3 : 3 ≤ ℓg) (hℓgM' : ℓg ∣ M')
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker) :
    H₁.index = Nat.totient q * (ℓg - 1) ∧ (-1 : (ZMod (q ^ 2 * M'))ˣ) ∉ H₁ := by sorry
