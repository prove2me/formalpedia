-- Prove2me | Theorems.Thm_ModularCurve_XOneP_forall_exists_sub_mem_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_x1_mul
-- name    : ModularCurve.XOneP.forall_exists_sub_mem_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/0d03b6e6-e9bd-50ec-9e21-c7c9ed114f7a
-- title:
--   Residue degree one at supersingular points over the Γ₀(p)-floor
-- statement:
--   Fix a prime $p$ and $M \ge 5$ with $p \nmid M$, let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and let $\zeta \in L$ be a primitive $p$-th root of unity. Let $K$ be the intermediate field of $L \subset \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the image, under the coefficientwise embedding $\mathrm{LaurentSeries}\,\mathbb{Q} \to \mathrm{LaurentSeries}\,L$, of the function field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137), and let $K_1$ be the analogous base change of [`ModularCurve.x1x0FunctionFieldC ℚ M p`](def/ModularCurve_X1.html#L142), the field generated over $\mathbb{Q}$ by the integral form ratios for $\Gamma_1(M) \cap \Gamma_0(p)$, with $K_1 \le K$. Let $A$ be a discrete valuation ring with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ is in the image of $A$, with uniformiser $\varpi$, and with $A$-algebra and scalar-tower structures on $K$ and $K_1$. Let $j \in K$ and $j_1 \in K_1$ be nonzero elements whose underlying Laurent series are both the coefficientwise image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). Write $B =$ `chartAlgFin A K j` for the subalgebra of $K$ of elements integral over $A[j]$, and similarly $B_1 \subset K_1$ for $j_1$, and let $\iota_F : B_1 \to B$ be an $A$-algebra map compatible with the inclusions into $\mathrm{LaurentSeries}\,L$. Let $y$ be a point of $\operatorname{Spec} B$ whose prime ideal contains the image of $\varpi$, and assume $y$ is supersingular in the sense that for every algebraically closed field $\Omega$ of characteristic $p$ and every ring homomorphism $\varphi : B \to \Omega$ with kernel the prime of $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet p Ω`](def/ModularCurve_SupersingularModuli.html#L7), i.e. every elliptic curve over $\Omega$ with that $j$-invariant has no nonzero $p$-torsion point. Then for every $s \in B$ there is $r \in B_1$ with $s - \iota_F(r)$ in the prime ideal of $y$.
--
--   The assertion is that the residue field extension $\kappa(\iota_F^{-1}y) \to \kappa(y)$ is surjective, i.e. has degree one: the $p$-part of the level of $X_1(Mp)$ contributes no residue extension above a supersingular point of the special fibre, the extension being totally ramified there. It is used in the identification of the point $y$ with its image on the $\Gamma_1(M) \cap \Gamma_0(p)$ floor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_forall_exists_sub_mem_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_x1_mul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

theorem ModularCurve.XOneP.forall_exists_sub_mem_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))

    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (hle : K₁ ≤ K)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (j₁ : ↥K₁) (hj₁ : ((j₁ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₁ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (ιF : ↥(chartAlgFin A (↥K₁) j₁) →ₐ[A] ↥(chartAlgFin A (↥K) j))
    (hιF : ∀ x, (((ιF x : ↥K) : LaurentSeries L)) = ((x : ↥K₁) : LaurentSeries L))

    (y : ↥(XFin A (↥K) j))
    (hyϖ : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y.asIdeal)

    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal → φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet p Ω) :
    ∀ s : ↥(chartAlgFin A (↥K) j), ∃ r : ↥(chartAlgFin A (↥K₁) j₁), s - ιF r ∈ y.asIdeal := by sorry
