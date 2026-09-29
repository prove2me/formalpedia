-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_levelAutBar_apply_eq_self_of_coe_eq_qExpand
-- name    : ModularCurve.FullLevel.levelAutBar_apply_eq_self_of_coe_eq_qExpand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/c475adcf-747d-56de-aa62-3d507042a2c1
-- title:
--   Level automorphisms fix q-expansion images from Γ₀(qM')
-- statement:
--   Let $q$ be a prime and $M'$ a nonzero natural number with $q \nmid M'$, and let $\zeta$ be an element of `Idx q`, i.e. of the set of primitive $q$-th roots of unity in $\overline{\mathbb{Q}}$ (taken as `AlgebraicClosure ℚ`). Let $\delta \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M')$ and have lower-left entry divisible by $q$. Let $g$ be a Laurent series over $\overline{\mathbb{Q}}$ lying in `laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 (q * M')))`, the subfield of $\overline{\mathbb{Q}}$-Laurent series generated over $\overline{\mathbb{Q}}$ by the coefficientwise images of the field generated over $\mathbb{Q}$ by the ratios $\mathrm{intSeriesC}\,\mathbb{Q}\,p_f/\mathrm{intSeriesC}\,\mathbb{Q}\,p_g$ attached to pairs of modular forms of equal weight on $\Gamma_0(qM')$ with integral $q$-expansions $p_f, p_g$, $\mathrm{intSeriesC}\,\mathbb{Q}\,p_g \neq 0$. Let $x$ be an element of `fieldBar q M'`, the $\overline{\mathbb{Q}}$-base change of the function field `xHFunctionField (q ^ 2 * M') (levelH q M')`, where `levelH q M'` is the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, and assume the underlying Laurent series of $x$ equals `qExpand (AlgebraicClosure ℚ) q g`, the series obtained from $g$ by multiplying all exponents by $q$. Then $x$ is fixed by the automorphism `levelAutBar q M' ζ δ` of `fieldBar q M'`, the $\overline{\mathbb{Q}}$-algebra automorphism chosen to satisfy `IsLevelAutBar q M' ζ δ` when such an automorphism exists and the identity otherwise; that predicate requires, for all weights $k$, all forms $f, g$ on $\Gamma_H(q^2M')$ with integral $q$-expansions $p_f, p_g$ and $\mathrm{intSeriesC}\,\mathbb{Q}\,p_g \neq 0$, and every ring embedding $\iota : \overline{\mathbb{Q}} \to \mathbb{C}$ with $\iota(\zeta) = e^{2\pi i/q}$, that the $\iota$-image of $\tau$ applied to the ratio $p_f/p_g$ transforms the $q$-expansion of $g \mid_k \mathrm{conjElem}\,q\,\delta$ into that of $f \mid_k \mathrm{conjElem}\,q\,\delta$.
--
--   The condition that the lower-left entry of $\delta \in \Gamma_0(M')$ be divisible by $q$ is the Borel condition at $q$, i.e. that the reduction of $\delta$ modulo $q$ fixes the point $[1:0]$ of $\mathbb{P}^1(\mathbb{F}_q)$; the statement says that the corresponding level automorphism of the level-$q^2M'$ function field acts trivially on the image of the level-$qM'$ function field under the degeneracy substitution $z \mapsto qz$. It is used by the three lemmas identifying the comap of `levelAutBar` for matrices whose reduction stabilises the line at infinity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_levelAutBar_apply_eq_self_of_coe_eq_qExpand.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.FullLevel.levelAutBar_apply_eq_self_of_coe_eq_qExpand
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 M') (hc : (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (g : LaurentSeries (AlgebraicClosure ℚ))
    (hg : g ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 (q * M'))))
    (x : fieldBar q M') (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) q g) :
    levelAutBar q M' ζ δ x = x := by sorry
