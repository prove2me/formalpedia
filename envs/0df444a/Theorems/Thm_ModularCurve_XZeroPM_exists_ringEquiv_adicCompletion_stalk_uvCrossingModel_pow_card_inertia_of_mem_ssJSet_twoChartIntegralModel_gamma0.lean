-- Prove2me | Theorems.Thm_ModularCurve_XZeroPM_exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_pow_card_inertia_of_mem_ssJSet_twoChartIntegralModel_gamma0
-- name    : ModularCurve.XZeroPM.exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_pow_card_inertia_of_mem_ssJSet_twoChartIntegralModel_gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/95b31bd1-d4c5-530c-a2b0-a3a1cb4b06ee
-- title:
--   Thickness of the X₀(Mp) node above a supersingular point
-- statement:
--   Fix a prime $p$ and $M \ge 5$ with $p \nmid M$, a field $L$ of characteristic zero that is a $p$-th cyclotomic extension of $\mathbb{Q}$, and a primitive $p$-th root of unity $\zeta \in L$. Let $K_1$ be the intermediate field of $\mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise images under [`ModularCurve.coeffEmb`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion field [`ModularCurve.x1x0FunctionFieldC ℚ M p`](def/ModularCurve_X1.html#L142), i.e. of the field generated over $\mathbb{Q}$ by the ratios of integral forms for $\Gamma_1(M) \cap \Gamma_0(p)$, and let $K_2$ be the analogous field for $\Gamma_0(Mp)$, with $K_2 \le K_1$. Let $A$ be a discrete valuation domain with fraction field $L$, with $p$ in its maximal ideal, with $\zeta$ in the image of $A$, with uniformiser $\varpi$ generating the maximal ideal, and with compatible algebra structures on $K_1$ and $K_2$. Let $j \in K_1$ and $j_2 \in K_2$ be nonzero elements whose Laurent series are both the image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). For a field $K$ and $0 \neq j \in K$, [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) is the pushout of the two chart maps, glueing $\operatorname{Spec}$ of the ring of elements of $K$ integral over $A[j]$ to $\operatorname{Spec}$ of the ring of elements integral over $A[j^{-1}]$; `toBase` is its structure morphism to $\operatorname{Spec} A$ and `ιFin` the open immersion of the finite chart. Assume given a morphism $\pi_2$ from the model for $(K_1,j)$ to the model for $(K_2,j_2)$ and an $A$-algebra map $\iota_{F_2}$ from the finite chart ring of $(K_2,j_2)$ to that of $(K_1,j)$ compatible with the Laurent series embeddings, such that $\pi_2$ followed by `toBase` for $(K_2,j_2)$ is `toBase` for $(K_1,j)$, $\operatorname{Spec} \iota_{F_2}$ followed by `ιFin` for $(K_2,j_2)$ equals `ιFin` for $(K_1,j)$ followed by $\pi_2$, the $\pi_2$-preimage of the open range of `ιFin` for $(K_2,j_2)$ is the open range of `ιFin` for $(K_1,j)$, $\pi_2$ and $\iota_{F_2}$ are finite, and an element of $K_1$ lies in the finite chart ring of $(K_1,j)$ exactly when it is integral over the image of the range of $\iota_{F_2}$. Let $z$ be a point of the model for $(K_1,j)$ at which the germ $\varpi z$ of the global section coming from $\varpi$ lies in the maximal ideal of the stalk, let $y$ be a point of the finite chart with image $z$, and assume that for every algebraically closed field $\Omega$ of characteristic $p$ and every ring homomorphism $\varphi$ from the finite chart ring to $\Omega$ with kernel the prime of $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet p Ω`](def/ModularCurve_SupersingularModuli.html#L7), the set of $j$-values all of whose elliptic curves over $\Omega$ have no nonzero $p$-torsion point. Finally let $G$ be a finite group acting faithfully on $K_1$ by semiring automorphisms whose fixed field is exactly $K_2$ (each $g$ fixes every element of $K_1$ lying in $K_2$, and any element fixed by all $g$ lies in $K_2$), with a compatible action on the finite chart ring, and put $\mathfrak{y} = y.\mathrm{asIdeal}$. Then there exist an adically complete discrete valuation domain $W_2$, a ring homomorphism $\sigma_2 : A \to W_2$ whose value at $\varpi$ generates the maximal ideal of $W_2$, and a ring isomorphism $e_2$ from the adic completion of the stalk of the model for $(K_2,j_2)$ at $\pi_2(z)$, with respect to its maximal ideal, onto [`ModularCurve.UVCrossingModel W₂ ((σ₂ ϖ) ^ ((p - 1) * Nat.card ↥(𝔶.inertia G)))`](def/ModularCurve_UVCrossingModel.html#L15), that is $W_2[[U,V]]/(UV - (\sigma_2\varpi)^{(p-1)\,|I|})$ where $I$ is the inertia subgroup of $\mathfrak{y}$ in $G$, such that $e_2$ carries the image in the completion of the germ at $\pi_2(z)$ of the global section coming from any $a \in A$ to the constant $\sigma_2(a)$.
--
--   This is the formal counterpart of the classical description of the integral model of $X_0(Mp)$ at the image of a supersingular point: an ordinary double point over an adically complete discrete valuation ring, of thickness $(p-1)$ times the order of the inertia group of the diamond covering at the point, the factor $p-1$ coming from the ramification of $p$ in $\mathbb{Q}(\zeta_p)$. It is used in the analysis of the model attached to $\Gamma_1(M) \cap \Gamma_0(p)$, feeding the two statements [`ModularCurve.XOneGammaZeroP.chartPackage_floorHom_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0_of_tame`](thm.html#ModularCurve.XOneGammaZeroP.chartPackage_floorHom_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0_of_tame) and [`ModularCurve.XOneGammaZeroP.exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_pow_of_mem_ssJSet_twoChartIntegralModel_of_tame`](thm.html#ModularCurve.XOneGammaZeroP.exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_pow_of_mem_ssJSet_twoChartIntegralModel_of_tame).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XZeroPM_exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_pow_card_inertia_of_mem_ssJSet_twoChartIntegralModel_gamma0.lean

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

theorem ModularCurve.XZeroPM.exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_pow_card_inertia_of_mem_ssJSet_twoChartIntegralModel_gamma0
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
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
    ∃ (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsDiscreteValuationRing W₂)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W₂) W₂) (σ₂ : A →+* W₂)
      (_ : IsLocalRing.maximalIdeal W₂ = Ideal.span {σ₂ ϖ})
      (e₂ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk (π₂.base z))) ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk (π₂.base z)) ≃+*
        ModularCurve.UVCrossingModel W₂ ((σ₂ ϖ) ^ ((p - 1) * Nat.card ↥(𝔶.inertia G)))),
      ∀ a : A, e₂ (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk (π₂.base z)) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk (π₂.base z))) ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk (π₂.base z)))
          (((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.germ ⊤ (π₂.base z) trivial).hom (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₂) j₂).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
        ModularCurve.UVCrossingModel.const ((σ₂ ϖ) ^ ((p - 1) * Nat.card ↥(𝔶.inertia G))) (σ₂ a) := by sorry
