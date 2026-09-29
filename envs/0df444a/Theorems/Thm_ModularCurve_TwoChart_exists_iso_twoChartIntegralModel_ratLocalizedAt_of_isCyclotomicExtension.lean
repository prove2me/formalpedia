-- Prove2me | Theorems.Thm_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_ratLocalizedAt_of_isCyclotomicExtension
-- name    : ModularCurve.TwoChart.exists_iso_twoChartIntegralModel_ratLocalizedAt_of_isCyclotomicExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/73d9663b-7013-59ef-b723-2df5973369e2
-- title:
--   Two-chart model over A versus integral model over ℤ₍ₚ₎
-- statement:
--   Let $p$ be a prime, let $L$ be a field of characteristic zero which is a $p$-cyclotomic extension of $\mathbb{Q}$, and let $A$ be a discrete valuation domain which is an $A$-algebra structure on $L$ realising $L$ as the fraction field of $A$, with $p$ lying in the maximal ideal of $A$; assume in addition that $A$ is an algebra over the subring $\mathbb{Z}_{(p)} =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ (the rationals whose denominator is coprime to $p$), compatibly with $L$. Let $K$ be an intermediate field between $L$ and the field of formal Laurent series $L((X))$, regarded as an $A$-algebra through the tower $A \to L \to K$, and let $j \in K$ be nonzero. Then there exist an isomorphism of schemes $w$ from [`ModularCurve.TwoChartModel A K j`](def/ModularCurve_TwoChartModel.html#L229) to [`AlgebraicCurve.TwoChartIntegralModel`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) over $\mathbb{Z}_{(p)}$ for the same data $(K, j)$ — both being the pushout of the two spectra of chart algebras along the middle chart — together with ring isomorphisms $e_{\mathrm{Fin}}$ and $e_{\mathrm{Inf}}$ between the corresponding chart algebras, namely between the elements of $K$ integral over $A[j]$ and those integral over $\mathbb{Z}_{(p)}[j]$, and likewise with $j^{-1}$ in place of $j$, such that: $e_{\mathrm{Fin}}$ and $e_{\mathrm{Inf}}$ are the identity when read inside $K$; $w$ followed by the structure morphism of the integral model to $\operatorname{Spec}\mathbb{Z}_{(p)}$ equals the structure morphism to $\operatorname{Spec} A$ followed by $\operatorname{Spec}$ of $\mathbb{Z}_{(p)} \to A$; each chart morphism of the source followed by $w$ equals $\operatorname{Spec}(e^{-1})$ followed by the corresponding chart morphism of the target, for the finite and the pole chart; and the preimage under $w$ of the open range of each chart morphism of the target is the open range of the corresponding chart morphism of the source.
--
--   This is the comparison statement asserting that, for $A$ the relevant cyclotomic discrete valuation ring above $\mathbb{Z}_{(p)}$, nothing is gained or lost by forming the two-chart model of $(K,j)$ over $A$ rather than the two-chart integral model over $\mathbb{Z}_{(p)}$: the chart algebras coincide as subrings of $K$ and the two pushouts are identified compatibly with charts and with the base. It is used in the study of points of $X_1(p)$ over Laurent series fields, where the Gauss reading of the two-chart model must be related to a model over $\mathbb{Z}_{(p)}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_ratLocalizedAt_of_isCyclotomicExtension.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_TwoChartModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ModularCurve.TwoChart.exists_iso_twoChartIntegralModel_ratLocalizedAt_of_isCyclotomicExtension
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra ↥(GaloisRep.ratLocalizedAt p) A] [IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A L]
    (K : IntermediateField L (LaurentSeries L)) [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)] :
    ∃ (w : ModularCurve.TwoChartModel A (↥K) j ≅ AlgebraicCurve.TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt p) (↥K) j)
      (eFin : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) (↥K) j))
      (eInf : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) ≃+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) (↥K) j)),

      (∀ x : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
        ((eFin x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) (↥K) j)) : ↥K) = (x : ↥K)) ∧
      (∀ x : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j),
        ((eInf x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) (↥K) j)) : ↥K) = (x : ↥K)) ∧

      w.hom ≫ AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) (↥K) j =
        ModularCurve.TwoChart.modelTo A (↥K) j ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) A)) ∧

      ModularCurve.TwoChart.ιFin A (↥K) j ≫ w.hom =
        Spec.map (CommRingCat.ofHom eFin.symm.toRingHom) ≫ AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) (↥K) j ∧
      ModularCurve.TwoChart.ιInf A (↥K) j ≫ w.hom =
        Spec.map (CommRingCat.ofHom eInf.symm.toRingHom) ≫ AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) (↥K) j ∧

      w.hom ⁻¹ᵁ (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) (↥K) j).opensRange = (ModularCurve.TwoChart.ιFin A (↥K) j).opensRange ∧
      w.hom ⁻¹ᵁ (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) (↥K) j).opensRange = (ModularCurve.TwoChart.ιInf A (↥K) j).opensRange := by sorry
