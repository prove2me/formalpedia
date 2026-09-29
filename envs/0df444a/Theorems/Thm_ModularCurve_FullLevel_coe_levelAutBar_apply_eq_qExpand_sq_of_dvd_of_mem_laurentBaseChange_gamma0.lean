-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0
-- name    : ModularCurve.FullLevel.coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/07bbc292-84fd-50f0-8612-d76d635f000d
-- title:
--   Level automorphism acts by Q ↦ Q^{q^2} when q ∣ a
-- statement:
--   Let $q$ be a prime and $M'$ a non-zero natural number with $q \nmid M'$, and let $\zeta$ be an element of `Idx q`, i.e. a primitive $q$-th root of unity in $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`. Let $\gamma \in \mathrm{SL}_2(\mathbb Z)$ lie in $\Gamma_0(M')$ and assume $q$ divides its $(0,0)$ entry. Let $g$ be a Laurent series over $\overline{\mathbb Q}$ lying in `laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))`, the subfield of $\overline{\mathbb Q}((Q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise images of the field generated over $\mathbb Q$ by the quotients $p_f/p_g$ of $q$-expansions of weight-$k$ modular forms on $\Gamma_0(M')$ with integral $q$-expansions $p_f,p_g$, $p_g \neq 0$. Let $x$ be an element of `fieldBar q M'`, the base change to $\overline{\mathbb Q}$ of the function field of $X_H(q^2M')$ for $H$ the kernel of $(\mathbb Z/q^2M')^\times \to (\mathbb Z/q)^\times$, whose underlying Laurent series is $g$. Then the Laurent series underlying `levelAutBar q M' ζ γ x` is $g$ substituted along $Q \mapsto Q^{q^2}$, that is, the image of $g$ under `qExpand (AlgebraicClosure ℚ) (q ^ 2)`, which multiplies all exponents by $q^2$. Here `levelAutBar q M' ζ γ` is the $\overline{\mathbb Q}$-automorphism of `fieldBar q M'` chosen, when one exists, to satisfy `IsLevelAutBar q M' ζ γ`: for every weight $k$, every pair of modular forms $f,g$ on $\Gamma_H(q^2M')$ with integral $q$-expansions $p_f,p_g$ and $p_g \neq 0$, and every embedding $\iota : \overline{\mathbb Q} \to \mathbb C$ with $\iota(\zeta) = e^{2\pi i/q}$, the $\iota$-image of the automorphism applied to $p_f/p_g$ equals the ratio of the $q$-expansions of $f \mid_k \mathrm{conjElem}(q,\gamma)$ and $g \mid_k \mathrm{conjElem}(q,\gamma)$; otherwise it is the identity.
--
--   This computes the effect of the level-$q$ automorphisms, indexed by a primitive $q$-th root of unity and by $\gamma \in \Gamma_0(M')$, on those elements of the full-level function field whose $q$-expansions already come from level $M'$: in the case $q \mid a$ the conjugated matrix $\mathrm{diag}(q,1)^{-1}\gamma\,\mathrm{diag}(q,1)$ acts on such expansions purely by the substitution $Q \mapsto Q^{q^2}$. It is used in the analysis of the orbits of the Igusa rings under these automorphisms, and hence in the recognition results for subfields of the full-level function field that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open ModularCurve.FullLevel
open CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.FullLevel.coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (ha : (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0)
    (g : LaurentSeries (AlgebraicClosure ℚ))
    (hg : g ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')))
    (x : fieldBar q M') (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = g) :
    ((levelAutBar q M' ζ γ x : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) (q ^ 2) g := by sorry
