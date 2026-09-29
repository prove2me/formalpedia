-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_exists_ratAlgEquiv_chartAlgFin_algEquiv_of_atkinLehner_generic
-- name    : ModularCurve.XHDRLevel.exists_ratAlgEquiv_chartAlgFin_algEquiv_of_atkinLehner_generic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/f4ec27c0-88dd-5340-9407-ebd06ba7b490
-- title:
--   Generic Atkin–Lehner automorphism descends to ℚ and to the j-chart
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing the kernel of the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ (every unit mapping to $1$ lies in $H$). Assume `jqModC ℚ`, the Laurent series $q^{-1}\cdot\mathrm{jNum}$ over $\mathbb{Q}$, lies in `qExpFunctionFieldC ℚ ⊤`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the full-level integral form ratios. Let $\theta$ be an $\overline{\mathbb{Q}}$-algebra automorphism of `xHFunctionFieldBar M H`, the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image `coeffEmb` of `xHFunctionField M H`, and suppose $\theta$ acts by $q \mapsto q^p$ (the map `qExpand`) on those elements whose $q$-expansion comes from `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)`, where `infSubgroup` is the image of $H$ under the reduction map. Then there are a $\mathbb{Q}$-algebra automorphism $\sigma$ of `qExpFunctionFieldC ℚ (ΓM M H)` and an `R p`-algebra automorphism `theta` of the chart algebra `chartAlgFin p (ΓM M H) hj`, consisting of the elements of that function field integral over `R p` adjoined with `jAt (ΓM M H) hj`, such that: $\theta$ agrees with the coefficient base change of $\sigma$ on coefficient-embedded rational elements; `theta` is the restriction of $\sigma$ to the chart algebra; and consequently $\theta$ and `theta` have the same effect on the $q$-expansion of any element of `xHFunctionFieldBar M H` that is the coefficient embedding of a chart element.
--
--   This is the rigidity-and-descent step for the Atkin–Lehner automorphism in the $p \,\|\, M$ case: an automorphism of the geometric function field of $X_H(M)$ acting as $q \mapsto q^p$ on the level $M/p$ subfield is already defined over $\mathbb{Q}$ and preserves the integral closure of the coefficient ring adjoined with $j$, so it can be read on the $j$-finite chart. It is used by the constructions of the two-chart Deligne–Rapoport model at $p$, in particular in identifying the chart action of the scheme automorphism $w$ and in the subsequent smooth-locus statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_exists_ratAlgEquiv_chartAlgFin_algEquiv_of_atkinLehner_generic.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve.XHDRLevel
open ModularCurve
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRLevel.exists_ratAlgEquiv_chartAlgFin_algEquiv_of_atkinLehner_generic
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
          ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ))) :
    ∃ (σ : ↥(qExpFunctionFieldC ℚ (ΓM M H)) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (ΓM M H)))
      (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj)),

      (∀ f : ↥(qExpFunctionFieldC ℚ (ΓM M H)),
        ((θ ⟨coeffEmb (AlgebraicClosure ℚ) (f : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) f.2⟩ :
          ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) (((σ f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ))) ∧

      (∀ b : ↥(chartAlgFin p (ΓM M H) hj),
        ((theta b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) = σ ((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H)))) ∧

      (∀ (b : ↥(chartAlgFin p (ΓM M H) hj)) (f : ↥(xHFunctionFieldBar M H)),
        (f : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) (((b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) (((theta b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)) := by sorry
