-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_atkinLehner_swap_and_exists_coe_eq_modularUnitSeries_and_isInftySide_smul_iff_isZeroSide_of_wgen
-- name    : ModularCurve.XHDRModelAtP.atkinLehner_swap_and_exists_coe_eq_modularUnitSeries_and_isInftySide_smul_iff_isZeroSide_of_wgen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/33c7ddb4-e63b-57ee-8ffa-db552e6c29d6
-- title:
--   Atkin–Lehner swap of j, j(qᵖ) and cuspidal sides
-- statement:
--   Fix a prime $p$ and a nonzero $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a proof `hj` that the $q$-expansion `jqModC ℚ` of $j$ lies in the field `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak{X}$ be an integral model datum `XHDRModelAtP p M H hpM hj` for $X_H(M)$ at $p$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, write $F_M$ for `xHFunctionFieldBar M H`, the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the $q$-expansions of `xHFunctionField M H`, and $F_{M/p}$ for the corresponding field at level $M/p$ with the image subgroup `infSubgroup p M H hpM`. Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of $F_M$ and $\alpha \colon F_{M/p} \to F_M$ a $\overline{\mathbb{Q}}$-algebra homomorphism, subject to: (i) for any two $\overline{\mathbb{Q}}$-points $y,y'$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base, if $y'$ followed by `𝔛.eeta`, the first pullback projection and `𝔛.w.hom` agrees with $y$ followed by `𝔛.eeta` and that projection, then the place attached to $y'$ is the image of the place attached to $y$ under the semilinear automorphism `SemilinearAut.ofAlgAut θ`; (ii) $\alpha$ is the identity on $q$-expansions; (iii) $\theta \circ \alpha$ acts on $q$-expansions by `qExpand _ p`, i.e. $q \mapsto q^p$. The conclusion has three parts. First, whenever $x, x' \in F_M$ have $q$-expansions `jqModC (AlgebraicClosure ℚ)` and `qExpand _ p (jqModC _)` respectively, then $\theta x = x'$ and $\theta x' = x$. Secondly, there is $G \in F_M$ whose $q$-expansion is the image under `coeffEmb` of `modularUnitSeries p`, the series $\Delta(q)/\Delta(q^p)$. Thirdly, for every place $C$ of $F_M$ over $\overline{\mathbb{Q}}$, the translate $\theta \bullet C$ is cuspidal (no $A$-integral value of a function with $q$-expansion $j$, in the sense of `JHPlaceSpecialization.IsCuspidal`) if and only if $C$ is cuspidal in the sense for $j(q^p)$ (`IsCuspidal'`), and conversely; and $\theta \bullet C$ lies on the $\infty$-side (cuspidal, with $x'/x^p$ taking at $C$ a value in $A$ of residue $1$) if and only if $C$ lies on the $0$-side ($j(q^p)$-cuspidal, with $x/x'^p$ taking a value in $A$ of residue $1$), and conversely.
--
--   This is the Atkin–Lehner part of Ogg's classical analysis at a prime exactly dividing the level: the involution $w_p$ interchanges $j(\tau)$ and $j(p\tau)$, the unit $\Delta(\tau)/\Delta(p\tau)$ is a function on the curve, and $w_p$ exchanges the cusps above $\infty$ with those above $0$. It feeds the construction of a vertical unit on the model at $p$ whose Atkin–Lehner transform has prescribed residues, used in the analysis of the reduction of $X_H(M)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_atkinLehner_swap_and_exists_coe_eq_modularUnitSeries_and_isInftySide_smul_iff_isZeroSide_of_wgen.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.atkinLehner_swap_and_exists_coe_eq_modularUnitSeries_and_isInftySide_smul_iff_isZeroSide_of_wgen
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    :

    (∀ x x' : ↥(xHFunctionFieldBar M H),
      ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
      ((x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) →
        θ x = x' ∧ θ x' = x) ∧

    (∃ G : ↥(xHFunctionFieldBar M H),
      ((G : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p)) ∧

    (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) (θ • C) ↔ JHPlaceSpecialization.IsCuspidal' (p := p) (M := M) (H := H) (A := A) C) ∧
      (JHPlaceSpecialization.IsCuspidal' (p := p) (M := M) (H := H) (A := A) (θ • C) ↔ JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) C) ∧
      (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) (θ • C) ↔ JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C) ∧
      (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) (θ • C) ↔ JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C)) := by sorry
