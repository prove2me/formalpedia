-- Prove2me | Theorems.Thm_ModularCurve_XOneGammaZeroP_isCyclic_inertia_and_not_dvd_card_inertia_of_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0_of_eq_three
-- name    : ModularCurve.XOneGammaZeroP.isCyclic_inertia_and_not_dvd_card_inertia_of_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/4adcc058-a7ed-5263-bb47-d3a7435c619f
-- title:
--   Cyclic inertia of order prime to 3 at supersingular points
-- statement:
--   Let $p$ be a prime with $p=3$, and let $M\ge 5$ be a natural number with $p\nmid M$ admitting a prime divisor $\ell$ with $\ell\not\equiv 1\pmod 3$. Let $L$ be a characteristic-zero field that is a $p$-th cyclotomic extension of $\mathbb{Q}$, with $\zeta\in L$ a primitive $p$-th root of unity. Inside $L$-Laurent series let $K_1$ be the subfield generated over $L$ by the coefficientwise image of the $q$-expansion field over $\mathbb{Q}$ of $\Gamma_1(M)\cap\Gamma_0(p)$ (the field generated over $\mathbb{Q}$ by the integral-form ratios for that group), and $K_2$ the corresponding field for $\Gamma_0(Mp)$, with $K_2\le K_1$. Let $A$ be a discrete valuation domain with fraction field $L$, with $p$ in its maximal ideal, with $\zeta$ in the image of $A$, and with uniformiser $\varpi$, compatibly an $A$-algebra structure on $K_1$ and $K_2$. Let $j\in K_1$ and $j_2\in K_2$ be the nonzero elements whose Laurent expansions are the image of the $q$-expansion of the modular invariant. Writing $\mathrm{chartAlgFin}$ for the ring of elements integral over $A[j]$ (resp. $A[j_2]$) and taking the two-chart integral models over $A$ obtained as pushouts of the two affine charts, let $\pi_2$ be a morphism from the model for $(K_1,j)$ to that for $(K_2,j_2)$, and $\iota F_2$ an $A$-algebra map of finite chart rings compatible with the Laurent embeddings; assume $\pi_2$ commutes with the structure morphisms to $\operatorname{Spec}A$, is compatible with $\iota F_2$ on the finite charts, pulls the finite chart back to the finite chart, is finite, that $\iota F_2$ is a finite ring map, and that the finite chart ring of $K_1$ is exactly the integral closure of the image of $\iota F_2$. Let $z$ be a point of the model for $(K_1,j)$ at which the germ of $\varpi$ lies in the maximal ideal of the stalk, and $y$ a point of the finite chart $\operatorname{Spec}(\mathrm{chartAlgFin})$ mapping to $z$, such that for every algebraically closed field $\Omega$ of characteristic $p$ and every ring homomorphism $\varphi$ from the finite chart ring to $\Omega$ with kernel the prime $y$, the value $\varphi(j)$ is supersingular in the sense that every elliptic Weierstrass curve over $\Omega$ with that $j$-invariant has no nonzero $p$-torsion point. Finally let $G$ be a finite group acting faithfully on $K_1$ by semiring automorphisms, fixing every element of $K_2$ and with fixed field contained in $K_2$, acting compatibly on the finite chart ring, and let $\mathfrak{y}$ be the prime ideal of that ring corresponding to $y$. Then the inertia subgroup of $G$ at $\mathfrak{y}$ is cyclic and its order is not divisible by $p$.
--
--   This is the $p=3$ case of the tame local analysis of the model of $X(\Gamma_1(M)\cap\Gamma_0(p))$ over $\Gamma_0(Mp)$ at a supersingular point of the special fibre: the inertia group of the diamond action at such a point is cyclic of order prime to $3$ once some prime divisor of $M$ is not $\equiv 1 \pmod 3$. It feeds the general tame statement [`ModularCurve.XOneGammaZeroP.isCyclic_inertia_and_not_dvd_card_inertia_of_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0_of_tame`](thm.html#ModularCurve.XOneGammaZeroP.isCyclic_inertia_and_not_dvd_card_inertia_of_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0_of_tame), used in describing the local structure of the modular curves at supersingular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneGammaZeroP_isCyclic_inertia_and_not_dvd_card_inertia_of_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0_of_eq_three.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

theorem ModularCurve.XOneGammaZeroP.isCyclic_inertia_and_not_dvd_card_inertia_of_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0_of_eq_three
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (hp : p = 3) (hℓ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 3 ≠ 1)
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
      RingHom.ker φ = y.asIdeal → φ (jChartFin A (↥K₁) j) ∈ ModularCurve.ssJSet p Ω)

    (G : Type) [Group G] [Fintype G] [MulSemiringAction G ↥K₁] [FaithfulSMul G ↥K₁]
    (hGfixK : ∀ (g : G) (x : ↥K₁), (x : LaurentSeries L) ∈ K₂ → g • x = x)
    (hGinvK : ∀ x : ↥K₁, (∀ g : G, g • x = x) → (x : LaurentSeries L) ∈ K₂)
    [MulSemiringAction G ↥(chartAlgFin A (↥K₁) j)]
    (hGA : ∀ (g : G) (a : ↥(chartAlgFin A (↥K₁) j)), ((g • a : ↥(chartAlgFin A (↥K₁) j)) : ↥K₁) = g • (a : ↥K₁))

    (𝔶 : Ideal ↥(chartAlgFin A (↥K₁) j)) (h𝔶 : 𝔶 = y.asIdeal) :
    IsCyclic ↥(𝔶.inertia G) ∧ ¬ p ∣ Nat.card ↥(𝔶.inertia G) := by sorry
