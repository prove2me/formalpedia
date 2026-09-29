-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_comap_eq_and_ramificationIdx_eq_one_and_isSeparable_of_over_gauss_gamma0_mul_xH_of_eq_three
-- name    : ModularCurve.FullLevel.exists_comap_eq_and_ramificationIdx_eq_one_and_isSeparable_of_over_gauss_gamma0_mul_xH_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/a70f9eb0-4b94-519f-b929-7a1005b1de55
-- title:
--   Branches over the Γ₀(3M') Gauss ring: conjugacy and tameness
-- statement:
--   Let $q$ be a prime with $q = 3$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $L$ be a field of characteristic zero containing a primitive $q$-th root of unity $\zeta$, such that some ring homomorphism $L \to \mathbb{C}$ carries $\zeta$ to $\exp(2\pi i/q)$. Inside $\mathrm{LaurentSeries}\,L$ consider the intermediate fields $K$, obtained by adjoining to $L$ the coefficientwise image of the $q$-expansion function field of $\Gamma_H(q^2M')$ with $H = \ker\big((\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times\big)$ (that field being generated over $\mathbb{Q}$ by the ratios $\mathrm{int}(p_f)/\mathrm{int}(p_g)$ of integral $q$-expansions of modular forms of equal weight), and, in the same way, $K_0$ and $K_0'$ built from the $q$-expansion function fields of $\Gamma_0(M')$ and of $\Gamma_0(qM')$ over $\mathbb{Q}$; it is assumed that $K_0 \le K_0' \le K$ and $K_0 \le K$. Let $A$ be a discrete valuation ring with fraction field $L$ such that $q$ lies in its maximal ideal and $\zeta$ lies in the image of $A$. Let $W_0 \subseteq K$, $O_0 \subseteq K_0$ and $O_0' \subseteq K_0'$ be the valuation subrings each characterised by the Gauss condition that $f$ belongs to it precisely when there are power series $x, y$ over $A$ with $y$ having nonzero reduction modulo the maximal ideal of $A$ and $f \cdot y = x$ as Laurent series over $L$. Then, with the algebra structures on $K$ over $K_0$ and $K_0'$ given by the inclusions, for every valuation subring $B$ of $K$ whose contraction to $K_0'$ is $O_0'$: first, there is an $L$-algebra automorphism $\tau$ of $K$ fixing $K_0'$ pointwise with $B = \tau^{-1}(W_0)$; and second, the contraction of $B$ to $K_0$ equals $O_0$, and for the resulting extension $O_0 \to B$ the ramification index of the maximal ideal of $O_0$ in the maximal ideal of $B$ is $1$, the map $O_0 \to B$ is local, and the residue field extension $\kappa(B)/\kappa(O_0)$ is separable.
--
--   This describes the branches of the covering $X_H(q^2M') \to X_0(M')$ lying over the Gauss (infinity-type) branch of the intermediate curve $X_0(qM')$ in the case $q = 3$: they form a single orbit under the $K_0'$-fixing $L$-automorphisms of the function field, and each is unramified with separable residue extension over the Γ₀(M')-level Gauss ring. It feeds the unramifiedness statements for height-one places of the $\Gamma_H(q^2M')$ function field used on the semistable-covering leg of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_comap_eq_and_ramificationIdx_eq_one_and_isSeparable_of_over_gauss_gamma0_mul_xH_of_eq_three.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_comap_eq_and_ramificationIdx_eq_one_and_isSeparable_of_over_gauss_gamma0_mul_xH_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
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
    (K₀' : IntermediateField L (LaurentSeries L))
    (hK₀' : K₀' = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q * M'))))
    (hle₀ : K₀ ≤ K₀') (hle' : K₀' ≤ K)
    (O₀' : ValuationSubring ↥K₀')
    (hO₀' : ∀ f : ↥K₀', f ∈ O₀' ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    letI : Algebra ↥K₀ ↥K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    letI : Algebra ↥K₀' ↥K := (IntermediateField.inclusion hle').toRingHom.toAlgebra
    ∀ (B : ValuationSubring ↥K), (∀ x : ↥K₀', algebraMap ↥K₀' ↥K x ∈ B ↔ x ∈ O₀') →

      (∃ τ : ↥K ≃ₐ[L] ↥K, (∀ x : ↥K₀', τ (algebraMap ↥K₀' ↥K x) = algebraMap ↥K₀' ↥K x) ∧
        B = W₀.comap τ.toAlgHom.toRingHom) ∧

      (∃ hB : ∀ x : ↥K₀, algebraMap ↥K₀ ↥K x ∈ B ↔ x ∈ O₀,
        letI : Algebra ↥O₀ ↥B :=
          (((algebraMap ↥K₀ ↥K).comp O₀.subtype).codRestrict B.toSubring fun a => (hB a).mpr a.2).toAlgebra
        (IsLocalRing.maximalIdeal ↥O₀).ramificationIdx' (IsLocalRing.maximalIdeal ↥B) = 1 ∧
        ∃ _ : IsLocalHom (algebraMap ↥O₀ ↥B),
          Algebra.IsSeparable (IsLocalRing.ResidueField ↥O₀) (IsLocalRing.ResidueField ↥B)) := by sorry
