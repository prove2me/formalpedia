-- Prove2me | Theorems.Thm_ModularCurve_XOneGammaZeroP_exists_ringEquiv_residueField_x1FunctionFieldC_of_gaussPresentation_x1x0
-- name    : ModularCurve.XOneGammaZeroP.exists_ringEquiv_residueField_x1FunctionFieldC_of_gaussPresentation_x1x0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/ecc5ddf1-286e-59f4-bad2-46df5253917f
-- title:
--   Gauss residue field of the Γ₀(p)-floor equals κ(X₁(M))
-- statement:
--   Let $p$ be a prime and $M \ge 5$ a nonzero natural number with $p \nmid M$; let $L$ be a field of characteristic zero which is a $\{p\}$-cyclotomic extension of $\mathbb{Q}$ and $\zeta \in L$ a primitive $p$-th root of unity. Let $K_1$ be an intermediate field of $L((q))$ over $L$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p)`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield of $L((q))$ generated over $L$ by the coefficientwise images under $\mathbb{Q} \to L$ of the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the set `intFormRatiosC ℚ (Gamma1 M ⊓ Gamma0 p)`. Let $A$ be a discrete valuation ring which is an $\mathbb{Q}$-algebra-free domain with fraction field $L$, with $p$ in its maximal ideal and $\zeta$ in the image of $A \to L$, and let $K_1$ carry a compatible $A$-algebra structure over $L$. Let $U$ be a valuation subring of $K_1$ characterised by Gauss presentations: $f \in U$ if and only if there are power series $x, y$ over $A$ with $y$ having nonzero reduction modulo the maximal ideal of $A$ and $f \cdot y = x$ in $L((q))$ after applying $A \to L$ coefficientwise; assume moreover that every element of $A$ maps into $U$. Then there is a ring isomorphism $\theta$ from the residue field of $U$ onto [`ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M`](def/ModularCurve_X1.html#L134), the subfield of $\kappa((q))$, $\kappa = A/\mathfrak{m}_A$, generated over $\kappa$ by `intFormRatiosC κ (Gamma1 M)`, such that: for every $f \in U$ and every Gauss presentation $f \cdot y = x$ as above, $\theta$ of the residue of $f$ is, as a Laurent series over $\kappa$, the quotient of the reduction of $x$ by the reduction of $y$; and for every $a \in A$, $\theta$ of the residue of the image of $a$ in $U$ is the image of the residue of $a$ under $\kappa \to$ `x1FunctionFieldC κ M`.
--
--   This identifies the residue field of the Gauss valuation ring of the $q$-expansion field of $X(\Gamma_1(M) \cap \Gamma_0(p))$ over a cyclotomic discrete valuation ring with the $q$-expansion function field of $X_1(M)$ over the residue field, the $\infty$-component of the Deligne–Rapoport reduction of the $\Gamma_0(p)$-level curve; the displayed compatibilities pin $\theta$ down on Gauss presentations and on constants. It is used in the analysis of inertia at supersingular points of the two-chart integral model of $X(\Gamma_1(M) \cap \Gamma_0(p))$ and in the comparison of Gauss residue fields with modular function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneGammaZeroP_exists_ringEquiv_residueField_x1FunctionFieldC_of_gaussPresentation_x1x0.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.XOneGammaZeroP.exists_ringEquiv_residueField_x1FunctionFieldC_of_gaussPresentation_x1x0
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    (U : ValuationSubring ↥K₁)
    (hU : ∀ f : ↥K₁, f ∈ U ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hA : ∀ a : A, algebraMap A ↥K₁ a ∈ U) :
    ∃ θ : IsLocalRing.ResidueField ↥U ≃+* ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M),
      (∀ (f : ↥U) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        ((f : ↥K₁) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        ((θ (IsLocalRing.residue ↥U f) : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M)) :
            LaurentSeries (IsLocalRing.ResidueField A))
          = HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
            HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A))) ∧
      (∀ a : A, θ (IsLocalRing.residue ↥U ⟨algebraMap A ↥K₁ a, hA a⟩) =
        algebraMap (IsLocalRing.ResidueField A) ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M)
          (IsLocalRing.residue A a)) := by sorry
