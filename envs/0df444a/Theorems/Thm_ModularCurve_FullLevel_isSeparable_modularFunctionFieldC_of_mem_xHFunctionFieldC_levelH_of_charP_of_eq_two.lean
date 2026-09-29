-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_isSeparable_modularFunctionFieldC_of_mem_xHFunctionFieldC_levelH_of_charP_of_eq_two
-- name    : ModularCurve.FullLevel.isSeparable_modularFunctionFieldC_of_mem_xHFunctionFieldC_levelH_of_charP_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/eba62d11-ffd5-561a-bdef-6e85ab03375d
-- title:
--   Separability over κ(̄ j,̄ j_{M'}) at q=2
-- statement:
--   Let $q$ be a prime which is equal to $2$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $\kappa$ be any field of characteristic $q$. Work inside the field of Laurent series $\kappa((q))$. Let $E_0 =$ [`ModularCurve.modularFunctionFieldC κ M'`](def/ModularCurve_JqCoeff.html#L61) be the intermediate field obtained by adjoining to $\kappa$ the two Laurent series `jqModC κ` (the series $q^{-1}$ times the reduction to $\kappa$ of the integral power series `jNum`, i.e. the reduced $q$-expansion of $j$) and `jqNModC κ M'`, its image under the substitution $q \mapsto q^{M'}$. Let $E_H =$ [`ModularCurve.xHFunctionFieldC κ (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')`](def/ModularCurve_XH.html#L76), that is `qExpFunctionFieldC κ (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))`: the field generated over $\kappa$ by the ratios `intFormRatiosC` of integral $q$-expansions at $\infty$ of forms of equal weight on the congruence subgroup $\Gamma_H$ attached to the subgroup $H =$ `levelH q M'` of $(\mathbb{Z}/q^2M')^\times$, which is by definition the kernel of the reduction map `ZMod.unitsMap` to $(\mathbb{Z}/q)^\times$. The theorem asserts that every $x \in E_H$ is separable over $E_0$, as an element of $\kappa((q))$ viewed as an extension of the subfield $E_0$.
--
--   This is the $q = 2$ case of the separability statement for the $\infty$-branch of the Igusa tower in characteristic $q$, stated for an arbitrary field $\kappa$ of characteristic $q$; the hypothesis $q = 2$ replaces the condition $q \ge 5$ of the generic case. It feeds the construction of a local homomorphism with separable residue field extension used on the tameness side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_isSeparable_modularFunctionFieldC_of_mem_xHFunctionFieldC_levelH_of_charP_of_eq_two.lean

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.FullLevel.isSeparable_modularFunctionFieldC_of_mem_xHFunctionFieldC_levelH_of_charP_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (κ : Type) [Field κ] [CharP κ q] :
    ∀ x ∈ ModularCurve.xHFunctionFieldC κ (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'),
      IsSeparable (↥(ModularCurve.modularFunctionFieldC κ M')) x := by sorry
