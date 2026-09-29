-- Prove2me | Theorems.Thm_ModularCurve_diamondAutHBar_algEquiv_algEquiv_eq_self_of_qExpand_of_diamondAutHBar_div_of_unitsMap_mul_eq_one
-- name    : ModularCurve.diamondAutHBar_algEquiv_algEquiv_eq_self_of_qExpand_of_diamondAutHBar_div_of_unitsMap_mul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/76bc95ab-b61f-5973-aef2-671eefdbff35
-- title:
--   Square law ⟨ d⟩ θ²=id for the Atkin–Lehner automorphism
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, and let $H \le (\mathbb{Z}/M)^\times$ contain every unit whose image under reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial. Write $E =$ `xHFunctionFieldBar M H` for the intermediate field of $\overline{\mathbb{Q}}$-Laurent series obtained by adjoining to $\overline{\mathbb{Q}}$ the image of the function field `xHFunctionField M H` under the coefficient embedding, and $E' =$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` for the corresponding field at level $M/p$ with group the image of $H$ under that reduction. Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of $E$ satisfying two clauses: (i) whenever $f \in E$ and $u \in E'$ have equal underlying Laurent series, $\theta f$ has underlying series `qExpand` $_p(u)$, the rescaling of $u$ by multiplication of exponents by $p$; (ii) for every unit $c$ of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$, and all $f \in E$, $u \in E'$ with the series of $f$ equal to `qExpand`$_p(u)$, the series of $\theta f$ equals that of `diamondAutHBar (M / p) (infSubgroup p M H hpM) c u`. Finally let $d \in (\mathbb{Z}/M)^\times$ be such that the residue of its image in $\mathbb{Z}/(M/p)$ times $p$ equals $1$. The conclusion is that for every $x \in E$ one has $\langle d\rangle(\theta(\theta x)) = x$, where $\langle d\rangle =$ `diamondAutHBar M H d` is the diamond automorphism, namely a choice of $\overline{\mathbb{Q}}$-automorphism of $E$ satisfying `IsDiamondAutHBar M H d` — acting on ratios of integral $q$-expansions of modular forms of level $\Gamma_H(M)$ through the slash action of any $\gamma \in \Gamma_0(M)$ with $\gamma_{00} \equiv d \bmod M$ — with the identity taken if no such automorphism exists.
--
--   This is the square law for the partial Atkin–Lehner involution at a prime exactly dividing the level: on the function field of $X_H(M)$ over $\overline{\mathbb{Q}}$, any automorphism $\theta$ with the two Atkin–Lehner pull-back clauses satisfies $\theta^2 = \langle p\rangle = \langle d\rangle^{-1}$ for $d\,p \equiv 1$ modulo $M/p$. It is used in the construction of the Atkin–Lehner datum on a generic chart of the de Rham model at $p$, via [`ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart`](thm.html#ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_diamondAutHBar_algEquiv_algEquiv_eq_self_of_qExpand_of_diamondAutHBar_div_of_unitsMap_mul_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.diamondAutHBar_algEquiv_algEquiv_eq_self_of_qExpand_of_diamondAutHBar_div_of_unitsMap_mul_eq_one
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))

    (hθα : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (hθβ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (c : (ZMod (M / p))ˣ), (c : ZMod (M / p)) = (p : ZMod (M / p)) →
        ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) →
          ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
            ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)))
    (d : (ZMod M)ˣ)
    (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (x : ↥(xHFunctionFieldBar M H)) :
    diamondAutHBar M H d (θ (θ x)) = x := by sorry
