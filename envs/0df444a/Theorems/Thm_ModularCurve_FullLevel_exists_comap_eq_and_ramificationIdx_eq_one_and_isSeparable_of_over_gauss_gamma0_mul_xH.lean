-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_comap_eq_and_ramificationIdx_eq_one_and_isSeparable_of_over_gauss_gamma0_mul_xH
-- name    : ModularCurve.FullLevel.exists_comap_eq_and_ramificationIdx_eq_one_and_isSeparable_of_over_gauss_gamma0_mul_xH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/f78d53eb-3856-56ed-bf3c-95fd4c7beb4a
-- title:
--   Branches over O₀' are Gauss conjugates, unramified over O₀
-- statement:
--   Let $q\ge 5$ be a prime, $M'$ a nonzero natural number with $q\nmid M'$, and $L$ a field of characteristic zero containing a primitive $q$-th root of unity $\zeta$, such that some ring homomorphism $L\to\mathbb{C}$ carries $\zeta$ to $\exp(2\pi i/q)$. Inside $\mathrm{LaurentSeries}\,L$ consider the intermediate fields $K$, $K_0$, $K_0'$ over $L$ obtained by `laurentBaseChange`, i.e. by adjoining to $L$ the coefficientwise images of: the field generated over $\mathbb{Q}$ by all ratios $f/g$ of integral $q$-expansions of modular forms of equal weight for $\Gamma_H(q^2M')$ with $H=\ker\big((\mathbb{Z}/q^2M')^\times\to(\mathbb{Z}/q)^\times\big)$ (this gives $K$), and the corresponding $q$-expansion fields for $\Gamma_0(M')$ (giving $K_0$) and for $\Gamma_0(qM')$ (giving $K_0'$), with $K_0\le K_0'\le K$ and $K_0\le K$. Let $A$ be a discrete valuation ring with fraction field $L$ such that $q$ lies in its maximal ideal and $\zeta$ is in the image of $A$. Let $W_0\subseteq K$, $O_0\subseteq K_0$, $O_0'\subseteq K_0'$ be the valuation subrings characterised by the Gauss condition: $f$ belongs to the subring exactly when $f\,y=x$ as Laurent series over $L$ for some power series $x,y$ over $A$ with $y$ nonzero modulo the maximal ideal of $A$. Then, $K$ being viewed as an algebra over $K_0$ and over $K_0'$ via the inclusions, for every valuation subring $B$ of $K$ whose contraction to $K_0'$ is $O_0'$: first, there is an $L$-algebra automorphism $\tau$ of $K$ fixing $K_0'$ pointwise with $B$ equal to the preimage of $W_0$ under $\tau$; and second, the contraction of $B$ to $K_0$ is $O_0$, and for the resulting $O_0$-algebra structure on $B$ the ramification index `ramificationIdx'` of the maximal ideal of $O_0$ in the maximal ideal of $B$ equals $1$, the structure map $O_0\to B$ is a local homomorphism, and the residue field extension of $B$ over that of $O_0$ is separable.
--
--   This is the tameness and transitivity statement for the branches of $X_H(q^2M')$ lying over the cuspidal (Gauss) place of $X_0(qM')$: all such branches are conjugate to the Gauss subring by level automorphisms fixing the $\Gamma_0(qM')$-floor, and each is unramified with separable residue extension over the Gauss place of the $\Gamma_0(M')$-floor. It feeds the unramifiedness results for places of height one on $X_H$ and the identification of the image of the $j$-chart at infinity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_comap_eq_and_ramificationIdx_eq_one_and_isSeparable_of_over_gauss_gamma0_mul_xH.lean

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

theorem ModularCurve.FullLevel.exists_comap_eq_and_ramificationIdx_eq_one_and_isSeparable_of_over_gauss_gamma0_mul_xH
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
