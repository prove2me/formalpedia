-- Prove2me | Theorems.Thm_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC_chartRing
-- name    : ModularCurve.exists_algEquiv_residueField_tensor_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC_chartRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/5a332850-fdaf-563c-8683-ce9d500ba2ab
-- title:
--   Igusa's theorem, pole chart: reduction of 𝒪_∞
-- statement:
--   Let $M\ge 1$ and let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ with $\Gamma_1(M)\le\Gamma\le\Gamma_0(M)$, let $p$ be a prime not dividing $M$, and write $R=$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of rationals whose denominator is coprime to $p$. Let $F=$ `qExpFunctionFieldC ℚ Γ` be the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the quotients $\mathrm{intSeriesC}\,p_f/\mathrm{intSeriesC}\,p_g$ of integral $q$-expansions of two modular forms of one weight on $\Gamma$, and let $j\in F$ be nonzero with Laurent series `jqModC ℚ`, i.e. $q^{-1}$ times the integral power series `jNum`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho\colon R\to A$ be a ring homomorphism compatible with the structure maps to $\overline{\mathbb{Q}}$ (so the inclusion). Let $x\in$ `qExpFunctionFieldC (ResidueField ↥A) Γ` $=\bar F$ have Laurent series `jqModC` over $\kappa$. Give $\kappa$ the $R$-algebra structure from $\rho$ followed by the residue map. Then there is a $\kappa$-algebra isomorphism $e_\infty$ from $\kappa\otimes_{R}\mathcal{O}_\infty$, where $\mathcal{O}_\infty=$ `chartAlgInf R F j` is the set of elements of $F$ integral over $R[j^{-1}]$, onto `CurveModel.chartRing κ {x⁻¹}`, the set of elements of $\bar F$ integral over $\kappa[x^{-1}]$, such that $e_\infty(1\otimes j^{-1})=x^{-1}$, and such that for every $b\in\mathcal{O}_\infty$ and every $y\in A((q))$ whose image in $\overline{\mathbb{Q}}((q))$ is the image of the $q$-expansion of $b$ under $\mathbb{Q}\to\overline{\mathbb{Q}}$, the Laurent series of $e_\infty(1\otimes b)$ is the coefficientwise reduction of $y$ modulo the maximal ideal of $A$.
--
--   This is the pole-chart half of Igusa's theorem in ring form for the modular curves between $X_1(M)$ and $X_0(M)$ at a prime $p\nmid M$: the chart ring at infinity of the two-chart integral model over $\mathbb{Z}_{(p)}$ has special fibre the normalisation of $\kappa[1/j]$ inside the field of reduced $q$-expansions, compatibly with coefficientwise reduction of $q$-expansions. It feeds, together with its finite-chart counterpart, the combined statement [`ModularCurve.exists_algEquiv_residueField_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_chartRing`](thm.html#ModularCurve.exists_algEquiv_residueField_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_chartRing), from which good reduction of the integral model away from the level is read off.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC_chartRing.lean

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
open IsLocalRing AlgebraicCurve ModularCurve
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_algEquiv_residueField_tensor_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC_chartRing
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
