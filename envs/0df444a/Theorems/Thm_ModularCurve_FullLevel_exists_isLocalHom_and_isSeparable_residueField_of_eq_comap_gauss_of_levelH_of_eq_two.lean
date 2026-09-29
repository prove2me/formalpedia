-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_isLocalHom_and_isSeparable_residueField_of_eq_comap_gauss_of_levelH_of_eq_two
-- name    : ModularCurve.FullLevel.exists_isLocalHom_and_isSeparable_residueField_of_eq_comap_gauss_of_levelH_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/bbc3bd01-952a-5a7e-a84d-3f00cc241847
-- title:
--   Gauss branch over the Γ₀(M') floor is separable, q=2
-- statement:
--   Let $q$ be a prime with $q = 2$, let $M' \ge 1$ satisfy $q \nmid M'$, and let $L$ be a field of characteristic zero containing a primitive $q$-th root of unity $\zeta$, assumed to admit a ring homomorphism $\iota : L \to \mathbb{C}$ with $\iota\zeta = \exp(2\pi i/q)$. Inside the Laurent series field $L((X))$ let $K$ be the intermediate field generated over $L$ by the coefficientwise image of the $q$-expansion function field attached to the congruence subgroup [`CohCarrier.GammaH`](def/CohCarrier_Level.html#L133) of level $q^2M'$ and group [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$; that function field is generated over $\mathbb{Q}$ by the quotients $\mathrm{intSeriesC}(p_f)/\mathrm{intSeriesC}(p_g)$ of integral $q$-expansions of two modular forms of equal weight for that group, with nonzero denominator. Let $K_0 \le K$ be the analogous base change of the $q$-expansion function field of $\Gamma_0(M')$. Let $A$ be a discrete valuation ring with fraction field $L$, with $q$ in its maximal ideal and $\zeta$ in the image of $A$. Let $W_0 \subseteq K$ and $O_0 \subseteq K_0$ be valuation subrings characterised by the Gauss condition: $f$ belongs to them exactly when $f \cdot y = x$ for some $x, y \in A[[X]]$ whose coefficients are read into $L$, with $y$ nonzero modulo the maximal ideal of $A$. Then, viewing $K$ as a $K_0$-algebra through the inclusion, for every $L$-algebra automorphism $\tau$ of $K$ fixing $K_0$ pointwise the following hold: an element of $K_0$ lies in $\tau^{-1}(W_0)$ precisely when it lies in $O_0$; the resulting ring map $O_0 \to \tau^{-1}(W_0)$ is a local homomorphism; and the induced extension of residue fields $\mathrm{ResidueField}(O_0) \to \mathrm{ResidueField}(\tau^{-1}(W_0))$ is separable.
--
--   This is the $q = 2$ case of the statement that the branches of the Igusa-type covering $X_H(q^2M') \to X_0(M')$ lying over the Gauss (cuspidal) valuation are unramified-in-the-residue-field sense well behaved: the Gauss ring of the floor is recovered by intersection, the inclusion is local, and the residue extension is separable. It feeds the computation of ramification indices and residue separability for the composite covering over the Gauss point of $\Gamma_0(M')$, used in the semistable-covering analysis of the full-level modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_isLocalHom_and_isSeparable_residueField_of_eq_comap_gauss_of_levelH_of_eq_two.lean

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

theorem ModularCurve.FullLevel.exists_isLocalHom_and_isSeparable_residueField_of_eq_comap_gauss_of_levelH_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    letI : Algebra ↥K₀ ↥K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    ∀ (τ : ↥K ≃ₐ[L] ↥K) (hτ : ∀ x : ↥K₀, τ (algebraMap ↥K₀ ↥K x) = algebraMap ↥K₀ ↥K x),
      ∃ hB : ∀ x : ↥K₀, algebraMap ↥K₀ ↥K x ∈ W₀.comap τ.toAlgHom.toRingHom ↔ x ∈ O₀,
        letI : Algebra ↥O₀ ↥(W₀.comap τ.toAlgHom.toRingHom) :=
          (((algebraMap ↥K₀ ↥K).comp O₀.subtype).codRestrict (W₀.comap τ.toAlgHom.toRingHom).toSubring
            fun a => (hB a).mpr a.2).toAlgebra
        ∃ _ : IsLocalHom (algebraMap ↥O₀ ↥(W₀.comap τ.toAlgHom.toRingHom)),
          Algebra.IsSeparable (IsLocalRing.ResidueField ↥O₀) (IsLocalRing.ResidueField ↥(W₀.comap τ.toAlgHom.toRingHom)) := by sorry
