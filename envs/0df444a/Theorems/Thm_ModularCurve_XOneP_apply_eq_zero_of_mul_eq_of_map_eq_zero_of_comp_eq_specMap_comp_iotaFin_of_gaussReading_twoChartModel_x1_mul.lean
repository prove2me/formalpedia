-- Prove2me | Theorems.Thm_ModularCurve_XOneP_apply_eq_zero_of_mul_eq_of_map_eq_zero_of_comp_eq_specMap_comp_iotaFin_of_gaussReading_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.apply_eq_zero_of_mul_eq_of_map_eq_zero_of_comp_eq_specMap_comp_iotaFin_of_gaussReading_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/eea10fee-1499-5b2b-a9a0-f58e2fa2297f
-- title:
--   Vanishing at k-points of a chart function with zero reduction
-- statement:
--   Fix a prime $p$, a natural number $M \neq 0$, a field $L$ of characteristic zero, an intermediate field $K$ of $L((q)) =$ `LaurentSeries L`, and a discrete valuation domain $A$ with an $A$-algebra structure on $L$ making $L$ its fraction field, together with a compatible $A$-algebra structure on $K$; fix $j \in K$ with $j \neq 0$ and a field $k$ that is an $A$-algebra. Let $c_1 \colon C_1 \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral, and let $i_1$ be a morphism from $C_1$ to the base change along $\operatorname{Spec} k \to \operatorname{Spec} A$ of the two-chart model [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), commuting with the structure morphisms to $\operatorname{Spec} k$. Let $w$ consist of a weight one modular form on $\Gamma_1(M)$ together with an integral $q$-expansion in $\mathbb{Z}[[q]]$ whose reduction `intSeriesC k` is nonzero, and let $\mathrm{Mdl}_1$ be a `CurveModel` over $k$ for the Igusa field [`ModularCurve.igusaFunctionFieldX1C k M w`](def/ModularCurve_IgusaFunctionFieldX1.html#L35), i.e. an integral scheme, proper and smooth of relative dimension $1$ over $\operatorname{Spec} k$, whose function field is identified with that intermediate field of $k((q))$ by a ring isomorphism compatible with $k$, whose closed points correspond bijectively to places with matching stalks, and in which every finite set of points lies in an affine open. Assume an isomorphism $e_1 \colon \mathrm{Mdl}_1.C \cong C_1$ over $\operatorname{Spec} k$ (i.e. $e_1$ followed by $c_1$ is $\mathrm{Mdl}_1.\mathrm{toBase}$), and that the preimage under $e_1$ followed by $i_1$ followed by the first projection of the open image of the finite chart [`ModularCurve.TwoChart.ιFin A K j`](def/ModularCurve_TwoChartModel.html#L231) is nonempty. Assume the Gauss reading hypothesis: for every $a$ in `chartAlgFin A K j`, the subalgebra of elements of $K$ integral over $A[j]$, and all $x, y \in A[[q]]$ with $\bar y \neq 0$ in $k[[q]]$ and $a \cdot y_L = x_L$ in $L((q))$, the pullback of $a$ along that composite, read through the germ at the generic point and the function field identification, equals $\bar x / \bar y$ in $k((q))$. Let $r \in$ `chartAlgFin A K j` and $x, y \in A[[q]]$ satisfy $\bar y \neq 0$, $r \cdot y_L = x_L$ in $L((q))$, and $\bar x = 0$ in $k[[q]]$. Finally let $c$ be a $k$-point of $C_1$ (a section of $c_1$) and $\psi \colon$ `chartAlgFin A K j` $\to k$ a ring homomorphism such that $c$ followed by $i_1$ and the first projection equals $\operatorname{Spec}(\psi)$ followed by the finite chart morphism. Then $\psi(r) = 0$.
--
--   This is the $q$-expansion principle modulo the maximal ideal of $A$ along the Gauss (cusp $\infty$) branch, in the finite chart and at the level of individual points: a chart function admitting a Gauss presentation whose numerator reduces to zero vanishes at every $k$-point of the cusp component that lies in the finite chart. It feeds the reduction step in the two statements [`ModularCurve.XOneP.exists_heckeDivOneBar_single_eq_sum_and_red_eq_frob_inv_smul_of_gaussReduces_of_surjective_residue_igusaModel_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_heckeDivOneBar_single_eq_sum_and_red_eq_frob_inv_smul_of_gaussReduces_of_surjective_residue_igusaModel_twoChartModel_x1_mul) and [`ModularCurve.XOneP.exists_heckeDivOneBar_single_eq_sum_and_red_eq_frob_inv_smul_of_gaussReduces_of_surjective_residue_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_heckeDivOneBar_single_eq_sum_and_red_eq_frob_inv_smul_of_gaussReduces_of_surjective_residue_twoChartModel_x1_mul), where Hecke divisors are compared with Frobenius twists.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_apply_eq_zero_of_mul_eq_of_map_eq_zero_of_comp_eq_specMap_comp_iotaFin_of_gaussReading_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.XOneP.apply_eq_zero_of_mul_eq_of_map_eq_zero_of_comp_eq_specMap_comp_iotaFin_of_gaussReading_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)]
    (k : Type) [Field k] [Algebra A k]
    (C₁ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))

    (w : ModularCurve.IntegralWeightOneForm k M)
    (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    [hne₁ : Nonempty (Scheme.Opens.toScheme ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hgauss₁ : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
      y.map (algebraMap A k) ≠ 0 →
      ((a : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      ((Mdl₁.ffEquiv.symm
          (Mdl₁.C.germToFunctionField ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) =
        HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) / HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k)))

    (r : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A)
    (hy : y.map (algebraMap A k) ≠ 0)
    (hr : ((r : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
      HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hx : x.map (algebraMap A k) = 0)

    (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁)
    (ψ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* k)
    (hc : c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j) :
    ψ r = 0 := by sorry
