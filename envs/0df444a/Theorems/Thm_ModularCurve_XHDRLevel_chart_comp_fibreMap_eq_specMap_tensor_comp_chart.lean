-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_chart_comp_fibreMap_eq_specMap_tensor_comp_chart
-- name    : ModularCurve.XHDRLevel.chart_comp_fibreMap_eq_specMap_tensor_comp_chart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/bfec44fa-446b-5f36-ac08-eeaf11b64b38
-- title:
--   Chart-pinned morphisms base-change to the κ-fibre charts
-- statement:
--   Fix a natural number $p$ and subgroups $\Gamma,\Gamma'$ of $\mathrm{SL}_2(\mathbb{Z})$, together with a hypothesis $hj$ asserting that the Laurent series `jqModC ℚ` lies in the intermediate field `qExpFunctionFieldC ℚ ⊤` of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the integral form ratios at full level; this datum defines the two-chart integral models $X\,p\,\Gamma\,hj$ and $X\,p\,\Gamma'\,hj$ with their structure morphisms `toBase` to $\operatorname{Spec} R_p$, and the finite chart algebras $\mathcal{O} =$ `chartAlgFin p Γ hj`, $\mathcal{O}' =$ `chartAlgFin p Γ' hj`, which are the subalgebras `chartAlg` of the respective $q$-expansion function fields over $R_p$. Let $\varphi$ be a morphism $X\,p\,\Gamma\,hj \to X\,p\,\Gamma'\,hj$ over $\operatorname{Spec} R_p$, that is, an element of `SchemeHomOver`, so its underlying morphism $\varphi_1$ satisfies $\varphi_1$ followed by `toBase p Γ' hj` equals `toBase p Γ hj`. Let $\psi : \mathcal{O}' \to \mathcal{O}$ be an $R_p$-algebra homomorphism pinning $\varphi$ on the finite charts, in the sense that `ιFin p Γ hj` followed by $\varphi_1$ equals $\operatorname{Spec}(\psi)$ followed by `ιFin p Γ' hj`. Let $\kappa$ be a commutative ring which is an $R_p$-algebra, and write $\mathfrak{X}_\kappa$ for `fibre`, the pullback of `toBase` along $\operatorname{Spec}$ of the structure map $R_p \to \kappa$. Let $c : \operatorname{Spec}(\kappa \otimes_{R_p} \mathcal{O}) \to \mathfrak{X}_\kappa$ be a morphism whose composite with the first pullback projection is $\operatorname{Spec}(\mathrm{includeRight})$ followed by `ιFin p Γ hj`, and whose composite with the second projection is $\operatorname{Spec}(\mathrm{includeLeftRingHom})$; let $c'$ satisfy the corresponding two conditions for $\Gamma'$ and $\mathcal{O}'$. Then $c$ followed by `fibreMap φ (algebraMap (R p) κ)`, the morphism of fibres induced by $\varphi_1$ and the identity on the base, equals $\operatorname{Spec}$ of $\mathrm{id}_\kappa \otimes \psi$ followed by $c'$.
--
--   This is the base-change compatibility of a chart-pinned morphism of two-chart integral models of modular curves over $\mathbb{Z}_{(p)}$: a morphism which on finite charts is given by an algebra map $\psi$ induces, on the fibres over an $R_p$-algebra $\kappa$, the morphism given on the base-changed finite charts by $\mathrm{id}_\kappa \otimes \psi$. It is used for the degeneracy (forgetful) maps and for Atkin–Lehner automorphisms in the analysis of the characteristic-$p$ fibres, and is cited in the study of Frobenius on the fibres and of chart images under Atkin–Lehner data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_chart_comp_fibreMap_eq_specMap_tensor_comp_chart.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel NeronModelInfra
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRLevel.chart_comp_fibreMap_eq_specMap_tensor_comp_chart
    (p : ℕ) {Γ Γ' : Subgroup SL(2, ℤ)} (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (φ : SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj))
    (ψ : ↥(chartAlgFin p Γ' hj) →ₐ[R p] ↥(chartAlgFin p Γ hj))
    (hφchart : ιFin p Γ hj ≫ φ.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ιFin p Γ' hj)
    (κ : Type) [CommRing κ] [Algebra (R p) κ]
    (c : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p Γ hj))) ⟶ fibre (Γ := Γ) (hj := hj) (algebraMap (R p) κ))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgFin p Γ hj))).toRingHom) ≫ ιFin p Γ hj)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgFin p Γ hj)))))
    (c' : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p Γ' hj))) ⟶ fibre (Γ := Γ') (hj := hj) (algebraMap (R p) κ))
    (hc'fst : c' ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgFin p Γ' hj))).toRingHom) ≫ ιFin p Γ' hj)
    (hc'snd : c' ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgFin p Γ' hj))))) :
    c ≫ fibreMap φ (algebraMap (R p) κ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) ψ).toRingHom) ≫ c' := by sorry
