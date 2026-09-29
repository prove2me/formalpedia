-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_isSeparable_modularFunctionFieldC_of_mem_xHFunctionFieldC_levelH_of_charP_of_eq_three
-- name    : ModularCurve.FullLevel.isSeparable_modularFunctionFieldC_of_mem_xHFunctionFieldC_levelH_of_charP_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/e72794bc-8c90-5dda-a5b6-93b19d58b3f8
-- title:
--   Igusa-level q-expansion field is separable over level-M' field, q=3
-- statement:
--   Let $q$ be a prime with $q = 3$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $\kappa$ be a field of characteristic $q$. Work inside the field $\kappa((X))$ of Laurent series over $\kappa$. On the one hand, let $H =$ [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22) be the kernel of the reduction map $(\mathbf{Z}/q^2M')^\times \to (\mathbf{Z}/q)^\times$, let [`CohCarrier.GammaH (q ^ 2 * M') H`](def/CohCarrier_Level.html#L133) be the subgroup of $\mathrm{SL}_2(\mathbf{Z})$ consisting of the elements of $\Gamma_0(q^2M')$ whose associated unit of $\mathbf{Z}/q^2M'$ (via [`CohCarrier.gamma0Units`](def/CohCarrier_Level.html#L121)) lies in $H$, and let $E_H =$ [`ModularCurve.xHFunctionFieldC κ (q ^ 2 * M') H`](def/ModularCurve_XH.html#L76) be the intermediate field of $\kappa((X))$ generated over $\kappa$ by the set `intFormRatiosC` attached to this group. On the other hand, let $E_0 =$ [`ModularCurve.modularFunctionFieldC κ M'`](def/ModularCurve_JqCoeff.html#L61) be the intermediate field generated over $\kappa$ by the two Laurent series `jqModC κ` (the coefficientwise reduction of the $q$-expansion of $j$) and `jqNModC κ M'` (its image under `qExpand` at level $M'$). The assertion is that every $x$ belonging to $E_H$ is separable over $E_0$, i.e. its minimal polynomial over $E_0$ is a separable polynomial. In the present case the proof establishes the stronger inclusion $E_H \le E_0$, so the separability is that of elements of the base field.
--
--   This is the $q = 3$ case of the separability statement for the $\infty$-branch of the Igusa tower over the level-$M'$ modular function field in characteristic $q$; at $q = 3$ the relevant covering degenerates, the Igusa-level field being already contained in the level-$M'$ field. It feeds the construction of a local homomorphism with separable residue field extension in [`ModularCurve.FullLevel.exists_isLocalHom_and_isSeparable_residueField_of_eq_comap_gauss_of_levelH_of_eq_three`](thm.html#ModularCurve.FullLevel.exists_isLocalHom_and_isSeparable_residueField_of_eq_comap_gauss_of_levelH_of_eq_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_isSeparable_modularFunctionFieldC_of_mem_xHFunctionFieldC_levelH_of_charP_of_eq_three.lean

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.FullLevel.isSeparable_modularFunctionFieldC_of_mem_xHFunctionFieldC_levelH_of_charP_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (κ : Type) [Field κ] [CharP κ q] :
    ∀ x ∈ ModularCurve.xHFunctionFieldC κ (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'),
      IsSeparable (↥(ModularCurve.modularFunctionFieldC κ M')) x := by sorry
