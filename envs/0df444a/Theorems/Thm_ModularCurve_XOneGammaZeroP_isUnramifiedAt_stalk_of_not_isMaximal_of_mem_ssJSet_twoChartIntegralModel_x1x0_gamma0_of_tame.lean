-- Prove2me | Theorems.Thm_ModularCurve_XOneGammaZeroP_isUnramifiedAt_stalk_of_not_isMaximal_of_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0_of_tame
-- name    : ModularCurve.XOneGammaZeroP.isUnramifiedAt_stalk_of_not_isMaximal_of_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0_of_tame
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/2cf65df9-90f2-5a59-82fe-465cfd1ba053
-- title:
--   Unramified off the closed point at supersingular points
-- statement:
--   Fix a prime $p$ and an integer $M\ge 5$ with $M\neq 0$ and $p\nmid M$, subject to two tameness conditions: either $p\neq 2$ or some prime $\ell\mid M$ has $\ell\not\equiv 1\pmod 4$, and if $p=3$ then some prime $\ell\mid M$ has $\ell\not\equiv 1\pmod 3$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb Q$ for $\{p\}$, with $\zeta\in L$ a primitive $p$-th root of unity. Let $K_1$ be the intermediate field of $L\subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise image of the $\mathbb Q$-field of $q$-expansions [`ModularCurve.x1x0FunctionFieldC ℚ M p`](def/ModularCurve_X1.html#L142) (the field generated over $\mathbb Q$ by the ratios `intFormRatiosC` for $\Gamma_1(M)\cap\Gamma_0(p)$), and $K_2$ the analogous field for $\Gamma_0(Mp)$, with $K_2\le K_1$. Let $A$ be a discrete valuation ring with fraction field $L$, with $p$ in its maximal ideal, $\zeta$ in the image of $A$, uniformiser $\varpi$ generating that maximal ideal, and with $A$-algebra structures on $K_1$ and $K_2$ compatible with $L$. Let $j\in K_1$ and $j_2\in K_2$ be nonzero elements whose Laurent series are both the coefficientwise image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). Consider the two-chart integral models $\mathcal Y=$ [`AlgebraicCurve.TwoChartIntegralModel A K₁ j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) and $\mathcal X_2=$ [`AlgebraicCurve.TwoChartIntegralModel A K₂ j₂`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), pushouts of the spectra of the chart algebras `chartAlgFin`, `chartAlgInf` (the integral closures in the field of $A[j]$, resp. $A[j^{-1}]$). Assume given a morphism $\pi_2\colon \mathcal Y\to\mathcal X_2$ and an $A$-algebra map $\iota_{F_2}\colon$ `chartAlgFin A K₂ j₂` $\to$ `chartAlgFin A K₁ j` inducing the inclusion on Laurent series, such that $\pi_2$ followed by `toBase A K₂ j₂` is `toBase A K₁ j`, that $\mathrm{Spec}(\iota_{F_2})$ followed by `ιFin A K₂ j₂` equals `ιFin A K₁ j` followed by $\pi_2$, that $\pi_2$ pulls the open range of `ιFin A K₂ j₂` back to that of `ιFin A K₁ j`, that $\pi_2$ and $\iota_{F_2}$ are finite, and that `chartAlgFin A K₁ j` consists exactly of the elements of $K_1$ integral over the image of the range of $\iota_{F_2}$. Let $z$ be a point of $\mathcal Y$ such that the germ at $z$ of the global section of $\mathcal Y$ obtained from $\varpi$ along `toBase A K₁ j` lies in the maximal ideal of the stalk at $z$, let $y$ be a point of $\mathrm{Spec}$ `chartAlgFin A K₁ j` mapping to $z$ under `ιFin A K₁ j`, and assume that for every algebraically closed field $\Omega$ of characteristic $p$ and every ring homomorphism $\varphi$ from `chartAlgFin A K₁ j` to $\Omega$ with kernel the prime corresponding to $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet p Ω`](def/ModularCurve_SupersingularModuli.html#L7), i.e. every elliptic Weierstrass curve over $\Omega$ with that $j$-invariant has no nonzero point killed by $p$. Then, for the algebra structure on the stalk of $\mathcal Y$ at $z$ over the stalk of $\mathcal X_2$ at $\pi_2(z)$ given by $\pi_2$'s stalk map, every prime ideal $\mathfrak q$ of the stalk at $z$ which is not maximal satisfies `Algebra.IsUnramifiedAt` for that algebra.
--
--   This is the local unramifiedness statement, in codimension at most one, for the degeneracy map from the model of $X(\Gamma_1(M)\cap\Gamma_0(p))$ to that of $X_0(Mp)$ over a ring of integers at $p$ in $\mathbb Q(\zeta_p)$, at a point of the special fibre whose $j$-invariant is supersingular: the generic point, the branches of the special fibre through $z$ and the characteristic-zero places specialising to $z$ are all unramified, only the closed point of the local ring being excluded. It feeds the construction of the chart package for the floor morphism at such supersingular points, [`ModularCurve.XOneGammaZeroP.chartPackage_floorHom_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0_of_tame`](thm.html#ModularCurve.XOneGammaZeroP.chartPackage_floorHom_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0_of_tame).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneGammaZeroP_isUnramifiedAt_stalk_of_not_isMaximal_of_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0_of_tame.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

theorem ModularCurve.XOneGammaZeroP.isUnramifiedAt_stalk_of_not_isMaximal_of_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0_of_tame
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (hp2 : p ≠ 2 ∨ ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 4 ≠ 1) (hlev3 : p = 3 → ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 3 ≠ 1)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))

    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (hle : K₂ ≤ K₁)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    [Algebra A ↥K₂] [IsScalarTower A L ↥K₂]
    (j : ↥K₁) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (j₂ : ↥K₂) (hj₂ : ((j₂ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₂ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (π₂ : (AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j) ⟶ (AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂))
    (ιF₂ : ↥(chartAlgFin A (↥K₂) j₂) →ₐ[A] ↥(chartAlgFin A (↥K₁) j))
    (hιF₂ : ∀ x, (((ιF₂ x : ↥K₁) : LaurentSeries L)) = ((x : ↥K₂) : LaurentSeries L))
    (hπbase : π₂ ≫ toBase A (↥K₂) j₂ = toBase A (↥K₁) j)
    (hπF : Spec.map (CommRingCat.ofHom ιF₂.toRingHom) ≫ ιFin A (↥K₂) j₂ = ιFin A (↥K₁) j ≫ π₂)
    (hpreF : π₂ ⁻¹ᵁ (ιFin A (↥K₂) j₂).opensRange = (ιFin A (↥K₁) j).opensRange)
    (hπfin : IsFinite π₂) (hιF₂fin : ιF₂.toRingHom.Finite)
    (hintF : ∀ x : ↥K₁, x ∈ chartAlgFin A (↥K₁) j ↔ IsIntegral ↥((ιF₂.range).map (chartAlgFin A (↥K₁) j).val) x)

    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j).presheaf.stalk z)
    (hϖz : ϖz = (((AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j).presheaf.germ ⊤ z trivial).hom (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₁) j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ))))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j).presheaf.stalk z))
    (y : ↥(XFin A (↥K₁) j)) (hy : (ιFin A (↥K₁) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K₁) j) →+* Ω),
      RingHom.ker φ = y.asIdeal → φ (jChartFin A (↥K₁) j) ∈ ModularCurve.ssJSet p Ω) :
    letI : Algebra ↑((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk (π₂.base z)) ↑((AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j).presheaf.stalk z) := (π₂.stalkMap z).hom.toAlgebra
    ∀ (𝔮 : Ideal ↑((AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j).presheaf.stalk z)) [𝔮.IsPrime], ¬ 𝔮.IsMaximal →
      Algebra.IsUnramifiedAt ↑((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk (π₂.base z)) 𝔮 := by sorry
