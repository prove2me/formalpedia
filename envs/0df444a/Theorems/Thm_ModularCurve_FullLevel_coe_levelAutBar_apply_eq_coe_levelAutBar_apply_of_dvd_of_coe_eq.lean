-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_coe_levelAutBar_apply_of_dvd_of_coe_eq
-- name    : ModularCurve.FullLevel.coe_levelAutBar_apply_eq_coe_levelAutBar_apply_of_dvd_of_coe_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/68fcdddf-88dc-5eef-b626-cdf12f76ff51
-- title:
--   Compatibility of level automorphisms under divisibility of levels
-- statement:
--   Fix a natural number $q$ carrying an instance that it is prime, and natural numbers $M'$, $M''$ with $M' \mid M''$ and $q \nmid M''$. For a level $M$ put $H_M \le (\mathbb{Z}/q^2M)^\times$ for the kernel of the reduction of units modulo $q$, and let $\mathrm{fieldBar}\,q\,M$ be the intermediate field of $\bar{\mathbb{Q}}((q)) / \bar{\mathbb{Q}}$ obtained by base change to $\bar{\mathbb{Q}}$ of the $q$-expansion function field $\mathrm{xHFunctionField}(q^2M, H_M)$. Assume `LevelAutInputs` at both levels $M'$ and $M''$, i.e. for every primitive $q$-th root of unity $\zeta$ in $\bar{\mathbb{Q}}$ and every $\gamma$ in $\Gamma_0$ of that level there exists a $\bar{\mathbb{Q}}$-algebra automorphism $\tau$ of the corresponding $\mathrm{fieldBar}$ satisfying `IsLevelAutBar`: for all weights $k$, all modular forms $f,g$ on $\Gamma_{H}(q^2M)$ with integral $q$-expansions $p_f,p_g$ and $\bar p_g \neq 0$, and every ring homomorphism $\iota : \bar{\mathbb{Q}} \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$, the $\iota$-image of $\tau(p_f/p_g)$ times the $q$-expansion of $g \mid_k \gamma^\sharp$ equals the $q$-expansion of $f \mid_k \gamma^\sharp$, where $\gamma^\sharp = \mathrm{conjElem}\,q\,\gamma$. Let $\zeta$ be such a root of unity, $\gamma \in SL(2,\mathbb{Z})$ with $\gamma \in \Gamma_0(M'')$, and let $u \in \mathrm{fieldBar}\,q\,M'$ and $u'' \in \mathrm{fieldBar}\,q\,M''$ have the same image in $\bar{\mathbb{Q}}((q))$. Then the chosen level automorphisms $\mathrm{levelAutBar}$ at levels $M''$ and $M'$ (each the chosen $\tau$ when one exists and the identity otherwise) send $u''$ and $u$ to elements with the same image in $\bar{\mathbb{Q}}((q))$.
--
--   This is the statement that the automorphism of the full-level modular function field attached to $\zeta$ and $\gamma$ at level $M''$ restricts, along the inclusion of function fields coming from $M' \mid M''$, to the corresponding automorphism at level $M'$. It is the function-field input for the equivariance of the degeneracy pull-back between full-level modular Jacobians, used in [`ModularCurve.FullLevel.exists_injective_linearMap_tateModule_jac_comp_tateGal_eq_and_comp_tateGL2_eq_of_dvd`](thm.html#ModularCurve.FullLevel.exists_injective_linearMap_tateModule_jac_comp_tateGal_eq_and_comp_tateGL2_eq_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_coe_levelAutBar_apply_of_dvd_of_coe_eq.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.coe_levelAutBar_apply_eq_coe_levelAutBar_apply_of_dvd_of_coe_eq
    (q : ℕ) [Fact q.Prime] (M' M'' : ℕ) (hM : M' ∣ M'') (hqM'' : ¬ q ∣ M'')
    (hLA : ModularCurve.FullLevel.LevelAutInputs q M') (hLA'' : ModularCurve.FullLevel.LevelAutInputs q M'')
    (ζ : ModularCurve.FullLevel.Idx q) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M'')
    (u : ModularCurve.FullLevel.fieldBar q M') (u'' : ModularCurve.FullLevel.fieldBar q M'')
    (hu : (u'' : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ))) :
    ((ModularCurve.FullLevel.levelAutBar q M'' ζ γ u'' : ModularCurve.FullLevel.fieldBar q M'') :
        LaurentSeries (AlgebraicClosure ℚ)) =
      ((ModularCurve.FullLevel.levelAutBar q M' ζ γ u : ModularCurve.FullLevel.fieldBar q M') :
        LaurentSeries (AlgebraicClosure ℚ)) := by sorry
