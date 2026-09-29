-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_exists_range_comp_subset_zeroLocus_jq_sub_pow
-- name    : ModularCurve.DRModelPackage.exists_range_comp_subset_zeroLocus_jq_sub_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/20914803-e3c5-5840-b678-2fe7f6363ceb
-- title:
--   Vanishing of j(qᵖ)-j(q)ᵖ on the p-fibre components
-- statement:
--   Let $p$ be a prime with $5 \le p$, let $\mathfrak{X}$ be a term of the structure `DRModelPackage p` (so in particular a bundle of properness, flatness, integrality, normality, rational and geometric curve models, sections and smooth-locus data for the two-chart integral model `DRModel p` $=$ `TwoChartIntegralModel ℤ (modularFunctionFieldFull p) (IgusaScheme.jFull p)` over $\operatorname{Spec}\mathbf{Z}$), and let $\kappa$ be an algebraically closed field of characteristic $p$. Let $a$ belong to the finite chart algebra `chartAlgFin ℤ (modularFunctionFieldFull p) (IgusaScheme.jFull p)`, that is, the subalgebra of elements of the field `modularFunctionFieldFull p` $\subset$ `LaurentSeries ℚ` integral over $\mathbf{Z}[j]$, where $j$ is `IgusaScheme.jFull p`, the class of `jq`; assume that the Laurent series underlying $a$ is `qExpand ℚ p jq - jq ^ p`, i.e. $j(q^p)-j(q)^p$. Write $P$ for the pullback of `DRModel.toBase p` along $\operatorname{Spec}\kappa \to \operatorname{Spec}\mathbf{Z}$, $U \subseteq P$ for the preimage under `pullback.fst` of the open image of $\top$ under `ιFin`, and $s \in \Gamma(P,U)$ for the section obtained from $a$ by the affine identification of the chart ring with the global sections of its spectrum, the isomorphism `(ιFin …).appIso ⊤`, and the map `(pullback.fst …).app`. Then there exist morphisms $C, D$ from the curve `(𝔛.ratModel κ).C` to $P$ such that either $C = \mathfrak{X}.\mathrm{compInf}\,\kappa$ and $D = \mathfrak{X}.\mathrm{compZero}\,\kappa$, or $C = \mathfrak{X}.\mathrm{compZero}\,\kappa$ and $D = \mathfrak{X}.\mathrm{compInf}\,\kappa$, with the following two properties. First, for every point $y$ of `(𝔛.ratModel κ).C` whose image $C(y)$ lies in $U$, the germ of $s$ at $C(y)$ lies in the maximal ideal of the local ring there. Second, for every $y$ with $D(y) \in U$ such that the germ of $s$ at $D(y)$ lies in the maximal ideal, there is $c \in \kappa$ with $c^{p^2} = c$ such that, whenever $D(y)$ lies in the open `chartFinOpenBC ℤ (modularFunctionFieldFull p) (IgusaScheme.jFull p) κ` (the preimage of the open range of `ιFin` in the base change to $\kappa$), the germ at $D(y)$ of `jCoordBC` minus the restriction of the global section `constSection … c` attached to $c$ lies in the maximal ideal.
--
--   This is the Frobenius/Verschiebung description of the geometric fibre at $p$ of the Deligne–Rapoport model of $X_0(p)$: on one of the two labelled components the modular function $j(q^p)-j(q)^p$ vanishes identically, while on the other it vanishes only at points whose $j$-coordinate is fixed by the square of Frobenius, i.e. lies in $\mathbf{F}_{p^2}$; the labelling of the two components is left undetermined. It is used in the identification of the two components of the $p$-fibre and, through that, in the computation of widths for the resolved model package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_exists_range_comp_subset_zeroLocus_jq_sub_pow.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve
open IsLocalRing

theorem ModularCurve.DRModelPackage.exists_range_comp_subset_zeroLocus_jq_sub_pow
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]

    (a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (ha : ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq - jq ^ p) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ (C D : (𝔛.ratModel κ).C ⟶ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))))),
      ((C = 𝔛.compInf κ ∧ D = 𝔛.compZero κ) ∨ (C = 𝔛.compZero κ ∧ D = 𝔛.compInf κ)) ∧

      (∀ y : ↥(𝔛.ratModel κ).C, ∀ hy : C.base y ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)),
        ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (C.base y) hy).hom
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) ∈ IsLocalRing.maximalIdeal _) ∧

      (∀ y : ↥(𝔛.ratModel κ).C, ∀ hy : D.base y ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)),
        ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (D.base y) hy).hom
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) ∈ IsLocalRing.maximalIdeal _ →
        ∃ c : κ, c ^ (p ^ 2) = c ∧
          ∀ hy' : D.base y ∈ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ,
            ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.germ
                (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ) (D.base y) hy').hom
              (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ -
                (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).presheaf.map (homOfLE le_top).op
                  (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ c)) ∈
              IsLocalRing.maximalIdeal _) := by sorry
