-- Prove2me | Theorems.Thm_ModularCurve_XOne_isDiscreteValuationRing_and_isFractionRing_of_mem_iff_exists_mul_residue_eq_of_gamma1_inf_gamma0_le
-- name    : ModularCurve.XOne.isDiscreteValuationRing_and_isFractionRing_of_mem_iff_exists_mul_residue_eq_of_gamma1_inf_gamma0_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/76462242-60b5-5a06-9db9-7842edc6ecb7
-- title:
--   Local ring of the Gauss sheet is a discrete valuation ring
-- statement:
--   Fix a prime $p$, an integer $M\ge 5$ with $p\nmid M$, and a subgroup $\Gamma\le \mathrm{SL}_2(\mathbb Z)$ with $\Gamma_1(M)\cap\Gamma_0(p)\le\Gamma\le\Gamma_1(M)$. Let $L$ be a field of characteristic zero that is a $p$-cyclotomic extension of $\mathbb Q$, and $\zeta\in L$ a primitive $p$-th root of unity. Let $K_1$ be the intermediate field of $L((q))$ generated over $L$ by the coefficientwise image of [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101), the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by the quotients $\,p_f/p_g\,$ of integral $q$-expansions of modular forms of equal weight for $\Gamma$. Let $A$ be a discrete valuation ring, a domain with fraction field $L$, with $p$ in its maximal ideal, $\zeta$ in the image of $A$, uniformiser $\varpi$, and let $K_1$ be an $A$-algebra compatibly with $L$. Let $j\in K_1$ be nonzero with Laurent expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), and write $A_1=$ `chartAlgFin A K₁ j` for the subalgebra of elements of $K_1$ integral over $A[j]$, so that $X=$ `XFin A K₁ j` is its spectrum. Let $W_0$ be a valuation subring of $K_1$ consisting exactly of those $f$ admitting a presentation $f\cdot \tilde y=\tilde x$ with $\tilde x,\tilde y\in A[[q]]$ (coefficients pushed to $L$) and $\tilde y$ nonzero modulo the maximal ideal of $A$, and assume $A_1\subseteq W_0$. Let $y$ be a point of $X$, i.e. a prime ideal of $A_1$, such that $\varpi\in y$, every element of $A_1$ lying in the maximal ideal of $W_0$ lies in $y$, and some element of $y$ does not lie in the maximal ideal of $W_0$. Finally let $R$ be the subring of the residue field of $W_0$ consisting of those $e$ for which there are $s,t\in A_1$ with $t\notin y$ and $e\cdot \overline t=\overline s$ under reduction $W_0\to\kappa(W_0)$. Then $R$ is a discrete valuation ring and $\kappa(W_0)$ is its field of fractions.
--
--   The ring $R$ is the localisation at $y$ of the image of the $j$-finite chart in the residue field of the Gauss valuation ring, i.e. the local ring at $y$ of the component of the special fibre passing through the cusp $\infty$; the assertion is that this component is regular at $y$ with function field $\kappa(W_0)$. It feeds the construction of valuation subrings of $\kappa(W_0)$ on the two-chart integral model for level $\Gamma_1(M)\cap\Gamma_0(p)$, where the special fibre itself is not integral at the supersingular crossings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOne_isDiscreteValuationRing_and_isFractionRing_of_mem_iff_exists_mul_residue_eq_of_gamma1_inf_gamma0_le.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

theorem ModularCurve.XOne.isDiscreteValuationRing_and_isFractionRing_of_mem_iff_exists_mul_residue_eq_of_gamma1_inf_gamma0_le
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓle : Γ ≤ CongruenceSubgroup.Gamma1 M)
    (hΓge : CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p ≤ Γ)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    (j : ↥K₁) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₀ : ValuationSubring ↥K₁)
    (hW₀ : ∀ f : ↥K₁, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hSW₀ : ∀ s : ↥(chartAlgFin A (↥K₁) j), (s : ↥K₁) ∈ W₀)

    (y : ↥(XFin A (↥K₁) j))
    (hyϖ : algebraMap A ↥(chartAlgFin A (↥K₁) j) ϖ ∈ y.asIdeal)
    (hy𝔓 : ∀ s : ↥(chartAlgFin A (↥K₁) j), (s : ↥K₁) ∈ W₀.nonunits → s ∈ y.asIdeal)
    (hy₀ : ∃ s : ↥(chartAlgFin A (↥K₁) j), s ∈ y.asIdeal ∧ (s : ↥K₁) ∉ W₀.nonunits)

    (R : Subring (IsLocalRing.ResidueField ↥W₀))
    (hR : ∀ e : IsLocalRing.ResidueField ↥W₀, e ∈ R ↔
      ∃ s t : ↥(chartAlgFin A (↥K₁) j), t ∉ y.asIdeal ∧
        e * IsLocalRing.residue ↥W₀ ⟨(t : ↥K₁), hSW₀ t⟩ = IsLocalRing.residue ↥W₀ ⟨(s : ↥K₁), hSW₀ s⟩) :
    IsDiscreteValuationRing ↥R ∧ IsFractionRing ↥R (IsLocalRing.ResidueField ↥W₀) := by sorry
