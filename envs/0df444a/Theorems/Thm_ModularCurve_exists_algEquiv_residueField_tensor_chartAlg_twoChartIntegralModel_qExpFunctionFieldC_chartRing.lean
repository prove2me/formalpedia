-- Prove2me | Theorems.Thm_ModularCurve_exists_algEquiv_residueField_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_chartRing
-- name    : ModularCurve.exists_algEquiv_residueField_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_chartRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/cf120f3a-e062-5789-b714-ffe285a15cf3
-- title:
--   Igusa reduction of the two chart rings, packaged
-- statement:
--   Fix $M \ge 1$ and a subgroup $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ with $\Gamma_1(M) \le \Gamma \le \Gamma_0(M)$, and a prime $p \nmid M$. Write $F =$ `qExpFunctionFieldC ℚ Γ`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the ratios `intFormRatiosC ℚ Γ`, and let $j \in F$ be nonzero with Laurent series `jqModC ℚ` $= q^{-1}\cdot(\text{reduction of } jNum)$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho$ be a ring map from $\mathbb{Z}_{(p)} =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) (the rationals with denominator coprime to $p$) into $A$ compatible with the inclusion into $\overline{\mathbb{Q}}$; regard $\kappa$ as a $\mathbb{Z}_{(p)}$-algebra via $\rho$ followed by the residue map. Let $x \in \bar F =$ `qExpFunctionFieldC κ Γ` have Laurent series `jqModC κ`. Then there are $\kappa$-algebra isomorphisms $\kappa \otimes_{\mathbb{Z}_{(p)}} \mathcal{O}_{\mathrm{fin}} \cong \widetilde{\kappa[x]}$ and $\kappa \otimes_{\mathbb{Z}_{(p)}} \mathcal{O}_{\mathrm{inf}} \cong \widetilde{\kappa[x^{-1}]}$, where $\mathcal{O}_{\mathrm{fin}}, \mathcal{O}_{\mathrm{inf}}$ are the elements of $F$ integral over $\mathbb{Z}_{(p)}[j]$, resp. $\mathbb{Z}_{(p)}[j^{-1}]$, and the targets are the elements of $\bar F$ integral over $\kappa[x]$, resp. $\kappa[x^{-1}]$, carrying $1 \otimes j \mapsto x$ and $1 \otimes j^{-1} \mapsto x^{-1}$, and such that whenever $b$ lies in the source algebra and $y \in A((q))$ has image in $\overline{\mathbb{Q}}((q))$ equal to the $q$-expansion of $b$, the $q$-expansion of the image of $1 \otimes b$ is the coefficientwise reduction `coeffMap (residue A) y` of $y$.
--
--   This is the ring-theoretic form of Igusa's good reduction theorem for the modular curve of level $\Gamma$ at a prime not dividing $M$: the special fibre of the two-chart integral model over $\mathbb{Z}_{(p)}$ built from $j$ and $j^{-1}$ is computed by the normalisations of $\kappa[x]$ and $\kappa[x^{-1}]$ inside the field of reduced $q$-expansions, with the identification compatible with reduction of $q$-expansions. It is used downstream in the study of the fibre maps and chart rings of $X_H$ in characteristic $p$, for instance in the statements about retractions of ring maps on `chartAlgFin` and about minimal primes of `chartAlgInf`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algEquiv_residueField_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_chartRing.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_JacJ1_ChartAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups TensorProduct
open IsLocalRing
open AlgebraicCurve
open ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_algEquiv_residueField_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_chartRing
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (j : ↥(qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    (x : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))
    (hx : (x : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A)) :
    letI := ((residue ↥A).comp ρ).toAlgebra
    (∃ eFin : ResidueField ↥A ⊗[↥(GaloisRep.ratLocalizedAt p)]
          ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) ≃ₐ[ResidueField ↥A]
        ↥(CurveModel.chartRing (ResidueField ↥A) ({(x : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))} :
          Set ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))),
      (eFin ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)]
        TwoChartIntegralModel.jChartFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)).1 = x ∧
      ∀ (b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j))
        (y : LaurentSeries ↥A),
        coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) →
        (((eFin ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b)).1 :
            ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) : LaurentSeries (ResidueField ↥A)) =
          coeffMap (residue ↥A) y) ∧
    (∃ eInf : ResidueField ↥A ⊗[↥(GaloisRep.ratLocalizedAt p)]
          ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) ≃ₐ[ResidueField ↥A]
        ↥(CurveModel.chartRing (ResidueField ↥A) ({(x : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))⁻¹} :
          Set ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))),
      (eInf ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)]
        TwoChartIntegralModel.jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)).1 = x⁻¹ ∧
      ∀ (b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j))
        (y : LaurentSeries ↥A),
        coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) →
        (((eInf ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b)).1 :
            ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) : LaurentSeries (ResidueField ↥A)) =
          coeffMap (residue ↥A) y) := by sorry
