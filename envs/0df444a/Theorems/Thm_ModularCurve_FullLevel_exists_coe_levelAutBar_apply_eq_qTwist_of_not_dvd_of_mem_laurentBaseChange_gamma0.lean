-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_coe_levelAutBar_apply_eq_qTwist_of_not_dvd_of_mem_laurentBaseChange_gamma0
-- name    : ModularCurve.FullLevel.exists_coe_levelAutBar_apply_eq_qTwist_of_not_dvd_of_mem_laurentBaseChange_gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/bfc91d98-aed8-5851-87ee-2c3b271a5fa5
-- title:
--   Level automorphism acts by root-of-unity twist when q∤ a
-- statement:
--   Let $q$ be a prime, $M'$ a nonzero natural number with $q\nmid M'$, and let $\zeta$ be an element of `Idx q`, i.e. a primitive $q$-th root of unity in $\overline{\mathbb Q}$ (an element of `primitiveRoots q (AlgebraicClosure ℚ)`), with underlying value $\zeta.val$. Let $\gamma\in\mathrm{SL}_2(\mathbb Z)$ lie in $\Gamma_0(M')$ and suppose $q$ does not divide the integer entry $\gamma_{00}$. Let $u$ be a unit of $\overline{\mathbb Q}$ whose value is $\zeta.val$. Then there exists an integer $k$ with the following property: for every Laurent series $g$ over $\overline{\mathbb Q}$ belonging to `laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))` — the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise images of the field generated over $\mathbb Q$ by the quotients $\mathrm{intSeriesC}\,p_f/\mathrm{intSeriesC}\,p_g$ of integral $q$-expansions of modular forms of equal weight for $\Gamma_0(M')$ — and for every $x$ in `fieldBar q M'`, the base change to $\overline{\mathbb Q}$ of the function field of level $q^2M'$ attached to the subgroup `levelH q M'` (the kernel of the unit reduction `ZMod.unitsMap (dvd_sq_mul q M')`), whose underlying Laurent series equals $g$, the Laurent series underlying $(\mathrm{levelAutBar}\ q\ M'\ \zeta\ \gamma)(x)$ is $\mathrm{qTwist}(u^k)(g)$, that is, the series whose $n$-th coefficient is $\zeta^{kn}g_n$. Here `levelAutBar q M' ζ γ` is the $\overline{\mathbb Q}$-algebra automorphism of `fieldBar q M'` chosen to satisfy the $q$-expansion compatibility predicate `IsLevelAutBar q M' ζ γ` when such an automorphism exists, and the identity otherwise.
--
--   This identifies the action of the level automorphism attached to $(\zeta,\gamma)$ on the subfield of functions of level $\Gamma_0(M')$, in the case where the top-left entry of $\gamma$ is prime to $q$: it is a uniform twist $q\mapsto\zeta^k q$ of $q$-expansions, with a single exponent $k$ serving all such functions (the complementary case $q\mid\gamma_{00}$ produces a substitution of $q$-power type instead). It feeds the lemmas comparing level structures through the Igusa ring, such as [`ModularCurve.FullLevel.eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing`](thm.html#ModularCurve.FullLevel.eq_of_forall_mem_iff_map_mem_of_integers_eq_igusaRing) and its variants for $q=2,3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_coe_levelAutBar_apply_eq_qTwist_of_not_dvd_of_mem_laurentBaseChange_gamma0.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CongruenceSubgroup
open ModularCurve.FullLevel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_coe_levelAutBar_apply_eq_qTwist_of_not_dvd_of_mem_laurentBaseChange_gamma0
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (ha : ¬ (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0)
    (u : (AlgebraicClosure ℚ)ˣ) (hu : (u : AlgebraicClosure ℚ) = ζ.val) :
    ∃ k : ℤ, ∀ (g : LaurentSeries (AlgebraicClosure ℚ)),
      g ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) →
      ∀ (x : fieldBar q M'), (x : LaurentSeries (AlgebraicClosure ℚ)) = g →
        ((levelAutBar q M' ζ γ x : fieldBar q M') : LaurentSeries (AlgebraicClosure ℚ)) =
          ModularCurve.qTwist (u ^ k) g := by sorry
