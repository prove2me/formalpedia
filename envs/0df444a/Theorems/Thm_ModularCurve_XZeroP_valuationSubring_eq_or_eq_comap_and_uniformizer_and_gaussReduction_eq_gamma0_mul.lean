-- Prove2me | Theorems.Thm_ModularCurve_XZeroP_valuationSubring_eq_or_eq_comap_and_uniformizer_and_gaussReduction_eq_gamma0_mul
-- name    : ModularCurve.XZeroP.valuationSubring_eq_or_eq_comap_and_uniformizer_and_gaussReduction_eq_gamma0_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/0e17f91d-a204-5af1-9fd1-e18b659edbb2
-- title:
--   Two Gauss valuation rings on X₀(Mp) above p
-- statement:
--   Let $p$ be a prime and $M \geq 5$ a natural number with $p \nmid M$; let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and $\zeta \in L$ a primitive $p$-th root of unity. Let $K$ be the intermediate field of $L \subseteq L((q))$ obtained as [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103), i.e. $L$-adjoining the coefficientwise image of the $q$-expansion function field [`ModularCurve.qExpFunctionFieldC ℚ`](def/ModularCurve_X1.html#L101) of $\Gamma_0(Mp)$ — the field generated over $\mathbb{Q}$ by the quotients of integral $q$-expansions of two modular forms of equal weight for $\Gamma_0(Mp)$, with nonzero denominator. Let $A$ be a discrete valuation ring with fraction field $L$, with $p$ in its maximal ideal, with $\zeta$ in the image of $A$, with $K$ an $A$-algebra compatibly with $L$, and let $\varpi$ generate the maximal ideal of $A$. Let $j \in K$ be the element whose Laurent series is the image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) $= q^{-1}\sum \dots$ under the coefficient embedding, $j \neq 0$. Let $W_0$ be a valuation subring of $K$ consisting exactly of those $f$ for which there are $x, y \in A[[q]]$ with $y$ of nonzero reduction modulo the maximal ideal of $A$ and $f \cdot y = x$ in $L((q))$ (the Gauss ring). Let $\sigma$ be an $L$-algebra automorphism of $K$ carrying $j$ to the Laurent series obtained from [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) by $q \mapsto q^p$, assumed to satisfy $\sigma^{*}W_0 \neq W_0$ and to have $\sigma^{*}W_0$ contain $P(j)$ and $P(j)^{-1}$ for every $P \in A[X]$ whose reduction modulo the maximal ideal of $A$ is nonzero. Call a valuation subring $V$ of $K$ admissible if it contains the image of $A$, sends the maximal ideal of $A$ into its nonunits, and contains $P(j)$ and $P(j)^{-1}$ for every $P \in A[X]$ of nonzero reduction. Then four assertions hold: (i) every admissible $V$ equals $W_0$ or $\sigma^{*}W_0$; (ii) for every admissible $V$, each nonunit $f$ of $V$ is of the form $\varpi g$ with $g \in V$, so the image of $\varpi$ generates the maximal ideal; (iii) if $R_0$ is an intermediate field of $\kappa \subseteq \kappa((q))$, $\kappa$ the residue field of $A$, whose elements are exactly the ratios $\bar{x}/\bar{y}$ arising from Gauss representations $f \cdot y = x$ of elements $f$ of $K$ as above, then $R_0$ is the $q$-expansion function field [`ModularCurve.qExpFunctionFieldC`](def/ModularCurve_X1.html#L101) of $\Gamma_0(M)$ over $\kappa$; and (iv) the relative degree of $K$ over the $L$-base change of the $q$-expansion function field of $\Gamma_0(M)$ over $\mathbb{Q}$ equals $p + 1$.
--
--   This is the local description, in function-field terms, of the two branches of the special fibre of the Deligne–Rapoport model of $X_0(Mp)$ over the discrete valuation ring $A \subseteq \mathbb{Q}(\zeta_p)$ above $p$, localised at the generic point of the $j$-line: exactly two valuation rings lie there, both unramified over $A$, the Gauss reductions of one of them recover the level-$M$ function field over the residue field, and $1 + p = p + 1$ matches the global degree. It feeds the residue-field and separability computations for the function fields of $X_1(M) \cap X_0(p)$ and the corresponding statements at composite level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XZeroP_valuationSubring_eq_or_eq_comap_and_uniformizer_and_gaussReduction_eq_gamma0_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ModularCurve.XZeroP.valuationSubring_eq_or_eq_comap_and_uniformizer_and_gaussReduction_eq_gamma0_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    [NeZero p]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (σ : ↥K ≃ₐ[L] ↥K)
    (hσj : ((σ j : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq))
    (hσW : W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ≠ W₀)
    (hσj' : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j P ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ∧
      (Polynomial.aeval j P)⁻¹ ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom) :

    (∀ V : ValuationSubring ↥K,
      (∀ a : A, algebraMap A ↥K a ∈ V) → (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits) →
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) →
      V = W₀ ∨ V = W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom) ∧

    (∀ V : ValuationSubring ↥K,
      (∀ a : A, algebraMap A ↥K a ∈ V) → (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits) →
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) →
      ∀ f : ↥K, f ∈ V.nonunits → ∃ g : ↥K, g ∈ V ∧ f = algebraMap A ↥K ϖ * g) ∧

    (∀ R₀ : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)),
      (∀ z : LaurentSeries (IsLocalRing.ResidueField A), z ∈ R₀ ↔
        ∃ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 ∧
          (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
            = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
            HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)) = z) →
      R₀ = ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) (CongruenceSubgroup.Gamma0 M)) ∧

    IntermediateField.relfinrank (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M))) K
      = p + 1 := by sorry
