-- Prove2me | Theorems.Thm_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing
-- name    : ModularCurve.exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/077ba4fc-29cc-5f80-bf47-1c396984d9d8
-- title:
--   Igusa reduction: finite chart of the Kroneckerian model
-- statement:
--   Fix $M \ge 1$ and a subgroup $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ with $\Gamma_1(M) \le \Gamma \le \Gamma_0(M)$, and a prime $p$ with $p \nmid M$. Write $F =$ `qExpFunctionFieldC ℚ Γ`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the quotients $f/g$ of $q$-expansions of modular forms of equal weight on $\Gamma$ having integral $q$-expansions, and let $j \in F$ be nonzero with Laurent series the series `jqModC ℚ` $= q^{-1}\cdot(E_4^3\cdot\eta^{-24})$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : \mathbb{Z}_{(p)} \to A$ be a ring homomorphism compatible with the inclusion $\mathbb{Z}_{(p)} \hookrightarrow \overline{\mathbb{Q}}$, where $\mathbb{Z}_{(p)} =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) is the subring of rationals with denominator coprime to $p$. Let $x \in$ `qExpFunctionFieldC κ Γ` have Laurent series `jqModC κ`. Viewing $\kappa$ as a $\mathbb{Z}_{(p)}$-algebra via $\rho$ followed by reduction, the assertion is that there is a $\kappa$-algebra isomorphism $e$ from $\kappa \otimes_{\mathbb{Z}_{(p)}} \mathcal{O}_{\mathrm{fin}}$, where $\mathcal{O}_{\mathrm{fin}}$ is the subalgebra of elements of $F$ integral over $\mathbb{Z}_{(p)}[j]$, onto the subalgebra of elements of `qExpFunctionFieldC κ Γ` integral over $\kappa[x]$, such that $e(1 \otimes j) = x$ and such that for every $b \in \mathcal{O}_{\mathrm{fin}}$ and every $y \in A((q))$ whose coefficientwise image in $\overline{\mathbb{Q}}((q))$ is the $q$-expansion of $b$, the Laurent series of $e(1 \otimes b)$ is the coefficientwise reduction of $y$ modulo the maximal ideal of $A$.
--
--   This is Igusa's theorem, in ring form, for the modular curve attached to $\Gamma$ at a prime $p$ not dividing the level: the finite chart of the integral two-chart model over $\mathbb{Z}_{(p)}$ has special fibre the normalisation of $\kappa[j]$ inside the field of reduced $q$-expansions, compatibly with reduction of coefficients. It is the finite-chart half of the combined two-chart statement [`ModularCurve.exists_algEquiv_residueField_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_chartRing`](thm.html#ModularCurve.exists_algEquiv_residueField_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_chartRing), which pairs it with its counterpart at the chart around the cusp.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing.lean

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

theorem ModularCurve.exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing
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
          coeffMap (residue ↥A) y) := by sorry
