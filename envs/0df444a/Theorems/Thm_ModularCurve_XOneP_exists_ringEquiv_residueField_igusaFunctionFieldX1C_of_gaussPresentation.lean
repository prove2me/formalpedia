-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_ringEquiv_residueField_igusaFunctionFieldX1C_of_gaussPresentation
-- name    : ModularCurve.XOneP.exists_ringEquiv_residueField_igusaFunctionFieldX1C_of_gaussPresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/c23c92ca-4347-5687-be98-081fbbe1cac2
-- title:
--   Residue field of a Gauss valuation subring is the Igusa field
-- statement:
--   Let $L$ be a field, $K$ an intermediate field of the Laurent series field $L((q))$ over $L$, and $A$ a discrete valuation ring which is an $A$-algebra domain with $L$ as its fraction field, together with an $A$-algebra structure on $K$ compatible with that on $L$; write $\kappa =$ `IsLocalRing.ResidueField A`. Let $W_0$ be a valuation subring of $K$ subject to: (hW₀) $f \in W_0$ if and only if $f$ admits a Gauss presentation, i.e. there are power series $x, y$ over $A$ with $\bar y \neq 0$ in $\kappa[[q]]$ and $f \cdot y = x$ inside $L((q))$ (images under $A \to L$); (hnu) for any such presentation of any $f \in K$, $f$ is a non-unit of $W_0$ exactly when $\bar x = 0$; and (hA) the image of $A$ in $K$ lies in $W_0$. Let $M$ be a natural number and $w$ an `IntegralWeightOneForm` over $\kappa$ of level $M$: a weight-one modular form on $\Gamma_1(M)$ together with an integral power series realising its $q$-expansion whose reduction to $\kappa$ is nonzero. Let $\mathrm{Ig} =$ `igusaFunctionFieldX1C` $\kappa\, M\, w$, the intermediate field of $\kappa((q))$ generated over $\kappa$ by `x1FunctionFieldC` $\kappa\, M$ (the $q$-expansion function field `qExpFunctionFieldC` for $\Gamma_1(M)$) together with the inverse of the Laurent series attached to $w$'s integral $q$-expansion over $\kappa$. Assume further (hmem) that for every $f \in K$ and every Gauss presentation $(x,y)$ of $f$ the quotient $\bar x / \bar y \in \kappa((q))$ lies in $\mathrm{Ig}$, and (hsurj) that every element of $\mathrm{Ig}$ is of this form $\bar x/\bar y$ for some $f \in K$ with Gauss presentation $(x,y)$. Then there is a ring isomorphism $\theta$ from the residue field of the local ring $W_0$ onto $\mathrm{Ig}$ such that for every $f \in W_0$ and every Gauss presentation $(x,y)$ of $f$ the image $\theta(\bar f)$, viewed in $\kappa((q))$, equals $\bar x / \bar y$, and such that for every $a \in A$ one has $\theta$ of the residue class of $a$ (as element of $W_0$ via hA) equal to the image of the residue of $a$ under the structure map $\kappa \to \mathrm{Ig}$.
--
--   This is the 'residue field of the Gauss branch equals the Igusa function field' half of the description of the special fibre of $X_1(Mp)$ at $p$, in the style of Katz–Mazur 13.11.3–13.11.4 and Edixhoven, read entirely through $q$-expansions. It is used in the construction of curve models for the components of the special fibre of the two-chart model of $X_1(Mp)$ and in the identification of the associated stalks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_ringEquiv_residueField_igusaFunctionFieldX1C_of_gaussPresentation.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.XOneP.exists_ringEquiv_residueField_igusaFunctionFieldX1C_of_gaussPresentation
    (L : Type) [Field L] (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hnu : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0))
    (hA : ∀ a : A, algebraMap A ↥K a ∈ W₀)
    (M : ℕ) (w : ModularCurve.IntegralWeightOneForm (IsLocalRing.ResidueField A) M)
    (hmem : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A))
        ∈ ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)
    (hsurj : ∀ z : LaurentSeries (IsLocalRing.ResidueField A),
      z ∈ ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w →
      ∃ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)) = z) :
    ∃ θ : IsLocalRing.ResidueField ↥W₀ ≃+* ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w),
      (∀ (f : ↥W₀) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        ((f : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        ((θ (IsLocalRing.residue ↥W₀ f) : ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)) :
            LaurentSeries (IsLocalRing.ResidueField A))
          = HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
            HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A))) ∧
      (∀ a : A, θ (IsLocalRing.residue ↥W₀ ⟨algebraMap A ↥K a, hA a⟩) =
        algebraMap (IsLocalRing.ResidueField A) ↥(ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w)
          (IsLocalRing.residue A a)) := by sorry
