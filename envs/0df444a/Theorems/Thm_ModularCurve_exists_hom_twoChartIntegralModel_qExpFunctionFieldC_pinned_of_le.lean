-- Prove2me | Theorems.Thm_ModularCurve_exists_hom_twoChartIntegralModel_qExpFunctionFieldC_pinned_of_le
-- name    : ModularCurve.exists_hom_twoChartIntegralModel_qExpFunctionFieldC_pinned_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/6a0f24dc-e274-5641-82ac-5cb642ccdf87
-- title:
--   Finite surjective morphism of two-chart integral models for Γ≤Γ'
-- statement:
--   Let $p$ be a prime, and let $\Gamma\le\Gamma'$ be subgroups of $\mathrm{SL}_2(\mathbb Z)$ with $\Gamma$ of finite index and $T\in\Gamma$. Let $R=\mathbb Z_{(p)}$ be the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of rationals whose denominator is coprime to $p$, and for a level $\Delta$ write $F(\Delta)=$ [`ModularCurve.qExpFunctionFieldC ℚ Δ`](def/ModularCurve_X1.html#L101), the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by the quotients of integral $q$-expansions of two modular forms of equal weight for $\Delta$. Let $j\in F(\Gamma)$ and $j'\in F(\Gamma')$ be nonzero elements (nonvanishing being assumed as instances) whose underlying Laurent series are both the $q$-expansion [`ModularCurve.jqModC ℚ`](def/ModularCurve_JqCoeff.html#L15) of the modular invariant. Write $\mathfrak X(\Delta)$ for `TwoChartIntegralModel R F(Δ) j_Δ`, the pushout gluing $\operatorname{Spec}$ of $A_{\mathrm{fin}}(\Delta)$, the integral closure of $R[j_\Delta]$ in $F(\Delta)$, to $\operatorname{Spec}$ of $A_{\mathrm{inf}}(\Delta)$, the integral closure of $R[j_\Delta^{-1}]$, along the middle chart. Then there exist a morphism of schemes $\pi\colon\mathfrak X(\Gamma)\to\mathfrak X(\Gamma')$ and $R$-algebra homomorphisms $\iota_0\colon A_{\mathrm{fin}}(\Gamma')\to A_{\mathrm{fin}}(\Gamma)$ and $\iota_\infty\colon A_{\mathrm{inf}}(\Gamma')\to A_{\mathrm{inf}}(\Gamma)$ such that: $\pi$ followed by the structure morphism $\mathfrak X(\Gamma')\to\operatorname{Spec}R$ is the structure morphism of $\mathfrak X(\Gamma)$; both $\iota_0$ and $\iota_\infty$ are pinned, i.e. they leave the underlying Laurent series of each element unchanged; the two chart squares commute, namely the finite chart immersion $\iota_{\mathrm{fin}}$ of $\mathfrak X(\Gamma)$ followed by $\pi$ equals $\operatorname{Spec}(\iota_0)$ followed by $\iota_{\mathrm{fin}}$ of $\mathfrak X(\Gamma')$, and likewise for the pole charts with $\iota_\infty$; $\pi$ is finite with surjective underlying map of topological spaces; and the $\pi$-preimage of the open range of the finite chart of $\mathfrak X(\Gamma')$ is exactly the open range of the finite chart of $\mathfrak X(\Gamma)$.
--
--   This is the functoriality of the two-chart integral model (the normalisation of the $j$-line over $\mathbb Z_{(p)}$ in a field of $q$-expansions) under the inclusion $F(\Gamma')\subseteq F(\Gamma)$ of function fields, in the form of a finite surjective degeneracy morphism compatible with both charts. It is used in the analysis of models of $X_H$ over $\mathbb Z_{(p)}$, in particular for the counting of minimal primes over the finite chart for $\Gamma_H$ and for the construction of generic charts adapted to Atkin–Lehner operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_hom_twoChartIntegralModel_qExpFunctionFieldC_pinned_of_le.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open scoped MatrixGroups
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_hom_twoChartIntegralModel_qExpFunctionFieldC_pinned_of_le
    (p : ℕ) [Fact p.Prime]
    (Γ Γ' : Subgroup SL(2, ℤ)) (hΓ : Γ ≤ Γ') [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (j : ↥(ModularCurve.qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = ModularCurve.jqModC ℚ)
    (j' : ↥(ModularCurve.qExpFunctionFieldC ℚ Γ')) [Fact (j' ≠ 0)] (hj' : (j' : LaurentSeries ℚ) = ModularCurve.jqModC ℚ) :
    ∃ (π : TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j ⟶
            TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ') j')
      (iota0 : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ') j')
          →ₐ[↥(GaloisRep.ratLocalizedAt p)]
        ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j))
      (iotaInf : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ') j')
          →ₐ[↥(GaloisRep.ratLocalizedAt p)]
        ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j)),

      π ≫ TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ') j' =
        TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j ∧

      (∀ b, (((iota0 b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j))
              : ↥(ModularCurve.qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) =
        ((b : ↥(ModularCurve.qExpFunctionFieldC ℚ Γ')) : LaurentSeries ℚ)) ∧
      TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j ≫ π =
        Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫
          TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ') j' ∧

      (∀ b, (((iotaInf b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j))
              : ↥(ModularCurve.qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) =
        ((b : ↥(ModularCurve.qExpFunctionFieldC ℚ Γ')) : LaurentSeries ℚ)) ∧
      TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j ≫ π =
        Spec.map (CommRingCat.ofHom iotaInf.toRingHom) ≫
          TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ') j' ∧

      IsFinite π ∧ Function.Surjective π.base ∧
      π ⁻¹ᵁ (TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ') j').opensRange =
        (TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.qExpFunctionFieldC ℚ Γ) j).opensRange := by sorry
