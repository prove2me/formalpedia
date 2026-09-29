-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_xHFunctionField_ker_le_and_jq_mem
-- name    : ModularCurve.FullLevel.Diamond.xHFunctionField_ker_le_and_jq_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/f7deb2ec-7263-5a04-8fe9-c4de3cf10d4b
-- title:
--   Inclusion of q-expansion function fields and j at level H₁
-- statement:
--   Fix a prime $q$, an integer $M' \neq 0$ in $\mathbb{N}$, and a prime $\ell_g$ with $\ell_g \mid M'$. Let $H_1$ be a subgroup of $(\mathbb{Z}/q^2M')^\times$ assumed to equal $\operatorname{levelH} q\,M' \sqcap \ker\big(\mathrm{ZMod.unitsMap}\big)$, that is, the intersection of the kernel of reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$ with the kernel of reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell_g)^\times$ (the latter coming from $\ell_g \mid q^2M'$ via $\ell_g \mid M'$). Write $H^\flat := \ker\big((\mathbb{Z}/M')^\times \to (\mathbb{Z}/\ell_g)^\times\big)$. The assertion is twofold. First, [`ModularCurve.xHFunctionField`](def/ModularCurve_XH.html#L79) $M'\,H^\flat$, the intermediate field of $\mathbb{Q} \subseteq \mathrm{LaurentSeries}\,\mathbb{Q}$ given by `qExpFunctionFieldC` of the group $\Gamma_{H^\flat}(M')$, is contained in [`ModularCurve.xHFunctionField`](def/ModularCurve_XH.html#L79) $(q^2M')\,H_1$, the corresponding intermediate field attached to $\Gamma_{H_1}(q^2M')$. Second, the Laurent series [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), namely $t^{-1}$ times the power series `jNumQ` (the $q$-expansion of the modular invariant $j$), lies in [`ModularCurve.xHFunctionField`](def/ModularCurve_XH.html#L79) $M'\,H^\flat$.
--
--   This records the elementary comparison between two levels in the tower used for the Diamond-type argument at full level: functions for the smaller group $\Gamma_{H_1}(q^2M')$ include those for $\Gamma_{H^\flat}(M')$, and the $j$-invariant, being of level one, sits in the smaller field. It is used by [`ModularCurve.FullLevel.Diamond.eq_of_isMaximal_of_mem_ssJSet_of_forall_coe_eq_qExpand_iff_chartAlgFin`](thm.html#ModularCurve.FullLevel.Diamond.eq_of_isMaximal_of_mem_ssJSet_of_forall_coe_eq_qExpand_iff_chartAlgFin) and by [`ModularCurve.FullLevel.Diamond.mem_of_coe_mem_nonunits_of_isMaximal_of_mem_ssJSet_chartAlgFin`](thm.html#ModularCurve.FullLevel.Diamond.mem_of_coe_mem_nonunits_of_isMaximal_of_mem_ssJSet_chartAlgFin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_xHFunctionField_ker_le_and_jq_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.FullLevel.Diamond.xHFunctionField_ker_le_and_jq_mem
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓgM' : ℓg ∣ M')
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker) :
    ModularCurve.xHFunctionField M' (ZMod.unitsMap hℓgM').ker ≤ ModularCurve.xHFunctionField (q ^ 2 * M') H₁ ∧
      ModularCurve.jq ∈ ModularCurve.xHFunctionField M' (ZMod.unitsMap hℓgM').ker := by sorry
