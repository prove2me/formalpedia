-- Prove2me | Theorems.Thm_ModularCurve_mem_iff_map_mem_and_mem_nonunits_iff_of_gaussPresentation_of_coe_eq_coeffMap
-- name    : ModularCurve.mem_iff_map_mem_and_mem_nonunits_iff_of_gaussPresentation_of_coe_eq_coeffMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/000847d2-3b9e-55c2-aaaf-199a60bd0839
-- title:
--   Gauss rings are compatible with coefficientwise extension of scalars
-- statement:
--   Fix a tower $\mathbb Q \subseteq k_0 \subseteq K_1 \subseteq \overline{\mathbb Q}$ of intermediate fields inside $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`, a valuation subring $A$ of $\overline{\mathbb Q}$ and a valuation subring $A_1$ of $K_1$ such that $x \in A_1$ holds for $x \in K_1$ exactly when the image of $x$ in $\overline{\mathbb Q}$ lies in $A$. Let $K$ be an intermediate field of $K_1 \subseteq K_1(\!(q)\!)$ and let $W_0$ be a valuation subring of $K$ characterised by the presentation property: $f \in W_0$ iff there are power series $x, y$ over $A_1$ with the reduction of $y$ along the residue map of $A_1$ nonzero, and $f \cdot y = x$ as Laurent series over $K_1$, the coefficients of $x$ and $y$ being pushed forward along $A_1 \to K_1$. Let $E$ be an intermediate field of $\overline{\mathbb Q} \subseteq \overline{\mathbb Q}(\!(q)\!)$ and let $O$ be a valuation subring of $E$ characterised by the analogous property with Laurent coefficients in $A$: $f \in O$ iff there are Laurent series $x, y$ over $A$ with the coefficientwise reduction `coeffMap (IsLocalRing.residue ↥A) y` nonzero and $f \cdot y = x$ after applying the coefficientwise inclusion $A \hookrightarrow \overline{\mathbb Q}$; here `coeffMap g` denotes the ring homomorphism on Laurent series induced by applying $g$ to each coefficient. Finally let $\varphi : K \to E$ be a ring homomorphism which on underlying Laurent series is given by applying $\mathrm{coeffMap}$ of the inclusion $K_1 \to \overline{\mathbb Q}$. The conclusion is twofold: for every $f \in K$ one has $f \in W_0$ iff $\varphi(f) \in O$, and $f$ is a non-unit of $W_0$ iff $\varphi(f)$ is a non-unit of $O$.
--
--   The rings $W_0$ and $O$ are the Gauss (valuation) rings attached to $A_1$ and to $A$ on the respective fields of Laurent series in $q$, and the statement says that both the valuation ring and its maximal ideal are detected identically before and after coefficientwise extension of scalars from $K_1$ to $\overline{\mathbb Q}$. It serves as the bridge between the $K_1$-level and the $\overline{\mathbb Q}$-level descriptions of the integral models of modular curves, and is used by the full-level results on two-chart integral models at good points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_iff_map_mem_and_mem_nonunits_iff_of_gaussPresentation_of_coe_eq_coeffMap.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.mem_iff_map_mem_and_mem_nonunits_iff_of_gaussPresentation_of_coe_eq_coeffMap
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)
    (K : IntermediateField ↥K₁ (LaurentSeries ↥K₁))

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries ↥A₁, y.map (IsLocalRing.residue ↥A₁) ≠ 0 ∧
      (f : LaurentSeries ↥K₁) * HahnSeries.ofPowerSeries ℤ ↥K₁ (y.map (algebraMap ↥A₁ ↥K₁))
        = HahnSeries.ofPowerSeries ℤ ↥K₁ (x.map (algebraMap ↥A₁ ↥K₁)))

    (E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (O : ValuationSubring ↥E)
    (hO : ∀ f : ↥E, f ∈ O ↔ ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
      (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)

    (φ : ↥K →+* ↥E)
    (hφ : ∀ f : ↥K, ((φ f : ↥E) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap (algebraMap ↥K₁ (AlgebraicClosure ℚ)) ((f : ↥K) : LaurentSeries ↥K₁)) :
    (∀ f : ↥K, f ∈ W₀ ↔ φ f ∈ O) ∧
    (∀ f : ↥K, (f : ↥K) ∈ W₀.nonunits ↔ (φ f : ↥E) ∈ O.nonunits) := by sorry
