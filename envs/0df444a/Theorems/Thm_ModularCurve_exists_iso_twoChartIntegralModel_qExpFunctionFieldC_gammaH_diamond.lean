-- Prove2me | Theorems.Thm_ModularCurve_exists_iso_twoChartIntegralModel_qExpFunctionFieldC_gammaH_diamond
-- name    : ModularCurve.exists_iso_twoChartIntegralModel_qExpFunctionFieldC_gammaH_diamond
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/18d22c0f-1ef1-516c-a123-6fcb90469d9b
-- title:
--   Diamond automorphisms of the two-chart integral model of X_H(M)
-- statement:
--   Fix $M \ge 1$, a subgroup $H \le (\mathbb Z/M)^\times$ and a prime $p$, and let $R =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) be the subring of $\mathbb Q$ of rationals whose denominator is coprime to $p$. Let $F$ be the intermediate field `qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)` of $\mathbb Q((q))$, namely the subfield generated over $\mathbb Q$ by the integral form ratios attached to the group $\Gamma_H(M) \le \mathrm{SL}_2(\mathbb Z)$ of those $\gamma \in \Gamma_0(M)$ whose image under `gamma0Units` lies in $H$. Let $j \in F$ be nonzero with underlying Laurent series the $q$-expansion `jqModC ℚ` $= q^{-1}\,(\text{integral power series }\mathrm{jNum})$, and assume the structure morphism `TwoChartIntegralModel.toBase` of $\mathfrak X =$ `TwoChartIntegralModel R F j` — the pushout of the two affine charts $\operatorname{Spec}$ of the integral closures of $R[j]$ and of $R[j^{-1}]$ in $F$ along their common overlap — to $\operatorname{Spec} R$ is separated. Let $\rho : \Gamma_0(M) \to \mathrm{Aut}_{\mathrm{ring}}(F)$ be a homomorphism which is trivial on $\Gamma_H(M)$ and fixes pointwise every element of $F$ whose Laurent series lies in `qExpFunctionFieldC ℚ (Gamma0 M)`. Then there exist families indexed by $d \in (\mathbb Z/M)^\times$: self-isomorphisms $\mathrm{dia}\,d$ of the scheme $\mathfrak X$, and $R$-algebra endomorphisms $\mathrm{diaFin}\,d$, $\mathrm{diaInf}\,d$ of the two chart algebras `chartAlgFin R F j` and `chartAlgInf R F j`, such that: $(\mathrm{dia}\,d).\mathrm{hom}$ followed by `toBase` equals `toBase`; $(\mathrm{dia}(dd')).\mathrm{hom}$ equals $(\mathrm{dia}\,d).\mathrm{hom}$ followed by $(\mathrm{dia}\,d').\mathrm{hom}$; $\mathrm{dia}\,d$ is the identity isomorphism for $d \in H$; and for all $d$ and all $\gamma \in \Gamma_0(M)$ whose upper-left entry reduces to $d$ modulo $M$, the endomorphisms $\mathrm{diaFin}\,d$ and $\mathrm{diaInf}\,d$ agree with $\rho\,\gamma$ after inclusion into $F$, and $\operatorname{Spec}$ of each of them followed by the corresponding chart immersion `ιFin`, resp. `ιInf`, equals that immersion followed by $(\mathrm{dia}\,d).\mathrm{inv}$.
--
--   This provides the diamond operators $\langle d \rangle$ on the two-chart integral model of $X_H(M)$ over $\mathbb Z_{(p)}$, obtained by transporting a given action $\rho$ of $\Gamma_0(M)$ on the $q$-expansion function field to the model, together with the compatibilities (multiplicativity, triviality on $H$, commutation with the structure morphism, and explicit description on each affine chart) needed downstream. It is used in the construction of the Deligne–Rapoport type model with Atkin–Lehner data, via [`ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart`](thm.html#ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_iso_twoChartIntegralModel_qExpFunctionFieldC_gammaH_diamond.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_iso_twoChartIntegralModel_qExpFunctionFieldC_gammaH_diamond
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (p : ℕ) [Fact p.Prime]
    (j : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
    [IsSeparated (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j)]
    (ρ : CongruenceSubgroup.Gamma0 M →* RingAut ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hρH : ∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H → ρ γ = 1)
    (hρ0 : ∀ (γ : CongruenceSubgroup.Gamma0 M) (x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))),
      (x : LaurentSeries ℚ) ∈ qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M) → ρ γ x = x) :
    ∃ (dia : (ZMod M)ˣ →
        (TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j ≅
          TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j))
      (diaFin : (ZMod M)ˣ →
        (↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j)
          →ₐ[↥(GaloisRep.ratLocalizedAt p)]
          ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j)))
      (diaInf : (ZMod M)ˣ →
        (↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j)
          →ₐ[↥(GaloisRep.ratLocalizedAt p)]
          ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j))),
      (∀ d, (dia d).hom ≫ TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j =
        TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j) ∧
      (∀ d d', (dia (d * d')).hom = (dia d).hom ≫ (dia d').hom) ∧
      (∀ d, d ∈ H → dia d = Iso.refl _) ∧
      (∀ (d : (ZMod M)ˣ) (γ : CongruenceSubgroup.Gamma0 M), (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = d →
        (∀ x, ((diaFin d x : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p)
            ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) = ρ γ x) ∧
        (∀ x, ((diaInf d x : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p)
            ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) = ρ γ x) ∧
        Spec.map (CommRingCat.ofHom (diaFin d).toRingHom) ≫
            TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j =
          TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j ≫ (dia d).inv ∧
        Spec.map (CommRingCat.ofHom (diaInf d).toRingHom) ≫
            TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j =
          TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j ≫ (dia d).inv) := by sorry
