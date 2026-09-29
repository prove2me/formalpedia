-- Prove2me | Theorems.Thm_ModularCurve_exists_gaussIntegral_lift_isIntegral_of_isIntegral_qExpFunctionFieldC_residueField_of_not_dvd
-- name    : ModularCurve.exists_gaussIntegral_lift_isIntegral_of_isIntegral_qExpFunctionFieldC_residueField_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/1102dc4a-6b70-5d5c-836e-1aa9ff71e6d7
-- title:
--   Lifting integrality over κ_A[jmath̄] to Gauss-integral q-expansions
-- statement:
--   Let $M\ge 1$ and let $\Gamma\le \mathrm{SL}_2(\mathbb{Z})$ satisfy $\Gamma_1(M)\le\Gamma\le\Gamma_0(M)$; let $p$ be a prime with $p\nmid M$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}=$ `AlgebraicClosure ℚ` with `A.LiesOverPrime p`, i.e. $p$ lies in the non-units of $A$. Write $\kappa_A$ for the residue field of $A$, $\mathrm{red}=$ `coeffMap (residue ↥A)` and $\iota=$ `coeffMap A.subtype` for the coefficientwise reduction $A((q))\to\kappa_A((q))$ and inclusion $A((q))\to\overline{\mathbb{Q}}((q))$, and $j_K=$ `jqModC K` for the series $q^{-1}\cdot(\mathrm{jNum})$ over $K$. Here `qExpFunctionFieldC K Γ` is the subfield of $K((q))$ generated over $K$ by the ratios $\mathrm{intSeriesC}\,p_f/\mathrm{intSeriesC}\,p_g$ attached to modular forms $f,g$ of equal weight for $\Gamma$ with integral $q$-expansions $p_f,p_g$ and nonzero denominator, and `laurentBaseChange` $\overline{\mathbb{Q}}$ `(qExpFunctionFieldC ℚ Γ)` is the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of `qExpFunctionFieldC ℚ Γ`. The assertion is the conjunction of two statements, identical except that the first uses $j$ and the second $j^{-1}$: for every $h\in$ `qExpFunctionFieldC` $\kappa_A\,\Gamma$ annihilated by a monic polynomial in one variable over $\kappa_A[j_{\kappa_A}]$ (respectively over $\kappa_A[j_{\kappa_A}^{-1}]$), there exist $f$ in `laurentBaseChange` $\overline{\mathbb{Q}}$ `(qExpFunctionFieldC ℚ Γ)` and $x,y\in A((q))$ with $\mathrm{red}(y)\neq 0$, $f\cdot\iota(y)=\iota(x)$, $\mathrm{red}(x)=h\cdot\mathrm{red}(y)$, and $f$ annihilated by a monic polynomial in one variable over $A[j_{\overline{\mathbb{Q}}}]$ (respectively over $A[j_{\overline{\mathbb{Q}}}^{-1}]$).
--
--   This is the lifting half of Igusa's good-reduction theorem for the modular curve of level $\Gamma$ at a prime $p\nmid M$, expressed in the currency of $q$-expansions and Deuring's constant reduction: elements of the function field in characteristic $p$ integral over $\kappa_A[\bar\jmath]$, or over $\kappa_A[\bar\jmath^{-1}]$, are reductions of elements of $\overline{\mathbb{Q}}\cdot F(\Gamma)$ lying in the Gauss valuation ring and integral over $A[j]$, respectively $A[j^{-1}]$. It feeds the construction of the two affine charts of the integral model, being cited by the two statements identifying the residue-field base change of the chart algebras of `twoChartIntegralModel` for `qExpFunctionFieldC`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_gaussIntegral_lift_isIntegral_of_isIntegral_qExpFunctionFieldC_residueField_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open IsLocalRing
open AlgebraicCurve
open ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_gaussIntegral_lift_isIntegral_of_isIntegral_qExpFunctionFieldC_residueField_of_not_dvd
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    (∀ h : LaurentSeries (ResidueField ↥A), h ∈ qExpFunctionFieldC (ResidueField ↥A) Γ →
      (∃ P : Polynomial (Polynomial (ResidueField ↥A)), P.Monic ∧
        Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A))) (jqModC (ResidueField ↥A)))
          h P = 0) →
      ∃ (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) (x y : LaurentSeries ↥A),
        coeffMap (residue ↥A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x ∧
        coeffMap (residue ↥A) x = h * coeffMap (residue ↥A) y ∧
        ∃ P : Polynomial (Polynomial ↥A), P.Monic ∧
          Polynomial.eval₂ (Polynomial.eval₂RingHom
            ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
            (jqModC (AlgebraicClosure ℚ))) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0) ∧
    (∀ h : LaurentSeries (ResidueField ↥A), h ∈ qExpFunctionFieldC (ResidueField ↥A) Γ →
      (∃ P : Polynomial (Polynomial (ResidueField ↥A)), P.Monic ∧
        Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A))) (jqModC (ResidueField ↥A))⁻¹)
          h P = 0) →
      ∃ (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) (x y : LaurentSeries ↥A),
        coeffMap (residue ↥A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x ∧
        coeffMap (residue ↥A) x = h * coeffMap (residue ↥A) y ∧
        ∃ P : Polynomial (Polynomial ↥A), P.Monic ∧
          Polynomial.eval₂ (Polynomial.eval₂RingHom
            ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
            (jqModC (AlgebraicClosure ℚ))⁻¹) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0) := by sorry
