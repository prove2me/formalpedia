-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_ramificationIdx_comap_gauss_eq_one_of_levelH
-- name    : ModularCurve.FullLevel.ramificationIdx_comap_gauss_eq_one_of_levelH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/41babbe6-02d3-5e00-b24b-ec1d28a339e0
-- title:
--   Conjugated Gauss rings are unramified over the base Gauss ring
-- statement:
--   Let $q$ be a prime with $5 \le q$, let $M'$ be a nonzero natural number with $q \nmid M'$, let $L$ be a field of characteristic zero containing a primitive $q$-th root of unity $\zeta$. Let $K \subseteq \mathrm{LaurentSeries}\,L$ be the intermediate field obtained by base change to $L$ (adjoining over $L$ the coefficientwise images under $\mathbb{Q} \to L$) of [`ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')`](def/ModularCurve_XH.html#L79), i.e. of the field generated over $\mathbb{Q}$ inside $\mathrm{LaurentSeries}\,\mathbb{Q}$ by the ratios of integral $q$-expansions of modular forms for the group $\Gamma_H(q^2M')$ attached to $H = \ker\bigl((\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times\bigr)$; and let $K_0$ be the corresponding base change of the $q$-expansion function field of $\Gamma_0(M')$ over $\mathbb{Q}$, with $K_0 \le K$. Let $A$ be a discrete valuation ring with fraction field $L$ such that $q$ lies in the maximal ideal of $A$ and $\zeta$ is in the image of $A$. Let $W_0$ be a valuation subring of $K$ consisting exactly of those $f$ admitting power series $x, y$ over $A$ with $y$ having nonzero reduction modulo the maximal ideal of $A$ and $f \cdot \hat y = \hat x$ in $\mathrm{LaurentSeries}\,L$ (hats denoting coefficientwise images in $L$), and let $O_0$ be the analogous valuation subring of $K_0$. Let $\tau$ be an $L$-algebra automorphism of $K$ such that, for $x \in K_0$, the image of $x$ in $K$ lies in $\tau^{-1}(W_0)$ precisely when $x \in O_0$. Then, with $O_0 \to \tau^{-1}(W_0)$ the algebra map induced by the inclusion $K_0 \subseteq K$, the ramification index (`ramificationIdx'`) of the maximal ideal of $O_0$ in the maximal ideal of $\tau^{-1}(W_0)$ equals $1$.
--
--   The rings $W_0$ and $O_0$ are the Gauss (Igusa) valuation rings at the cusp $\infty$ on the level-$H$ modular function field and on its $\Gamma_0(M')$ floor; the statement says that any conjugate of $W_0$ by an $L$-automorphism of the level field which lies over $O_0$ is unramified over $O_0$. It is used in [`ModularCurve.FullLevel.exists_comap_eq_and_ramificationIdx_eq_one_and_isSeparable_of_over_gauss_gamma0_mul_xH`](thm.html#ModularCurve.FullLevel.exists_comap_eq_and_ramificationIdx_eq_one_and_isSeparable_of_over_gauss_gamma0_mul_xH), part of the analysis of the valuation rings of the level field above the Gauss ring of the floor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_ramificationIdx_comap_gauss_eq_one_of_levelH.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

open scoped MatrixGroups

theorem ModularCurve.FullLevel.ramificationIdx_comap_gauss_eq_one_of_levelH
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (hle : K₀ ≤ K)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))

    (O₀ : ValuationSubring ↥K₀)
    (hO₀ : ∀ f : ↥K₀, f ∈ O₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (τ : ↥K ≃ₐ[L] ↥K)
    (hB : letI : Algebra ↥K₀ ↥K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
      ∀ x : ↥K₀, algebraMap ↥K₀ ↥K x ∈ W₀.comap τ.toAlgHom.toRingHom ↔ x ∈ O₀) :
    letI : Algebra ↥K₀ ↥K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    letI : Algebra ↥O₀ ↥(W₀.comap τ.toAlgHom.toRingHom) :=
      (((algebraMap ↥K₀ ↥K).comp O₀.subtype).codRestrict (W₀.comap τ.toAlgHom.toRingHom).toSubring
        fun a => (hB a).mpr a.2).toAlgebra
    (maximalIdeal ↥O₀).ramificationIdx' (maximalIdeal ↥(W₀.comap τ.toAlgHom.toRingHom)) = 1 := by sorry
