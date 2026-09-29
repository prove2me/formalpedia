-- Prove2me | Theorems.Thm_ModularCurve_exists_subfield_valuationSubring_laurentSeries_gauss_of_isDiscreteValuationRing
-- name    : ModularCurve.exists_subfield_valuationSubring_laurentSeries_gauss_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/f789153a-f0c4-56cf-9b28-6b7bc46ef62b
-- title:
--   Gauss valuation ring inside L((q)) over a DVR subring
-- statement:
--   Let $L$ be a field and let $A_0 \subseteq L$ be a valuation subring whose underlying ring is a discrete valuation ring. The assertion is the existence of a subfield $L_2$ of the field $L((q))$ of formal Laurent series over $L$ and of a valuation subring $W_2$ of $L_2$ satisfying three explicit membership criteria, where a power series $z \in A_0[[q]]$ is sent into $L((q))$ by applying the inclusion $A_0 \to L$ to its coefficients and then regarding the resulting element of $L[[q]]$ as a Laurent series. First, a Laurent series $f$ lies in $L_2$ if and only if there are $x, y \in A_0[[q]]$ with $y \neq 0$ and $f \cdot y = x$ in $L((q))$; so $L_2$ is the field of fractions of $A_0[[q]]$ inside $L((q))$. Second, an element $f$ of $L_2$ lies in $W_2$ if and only if there are $x, y \in A_0[[q]]$ with $f \cdot y = x$ and with the coefficientwise reduction of $y$ modulo the maximal ideal of $A_0$ non-zero. Third, $f$ lies in the set of non-units of $W_2$, that is in its maximal ideal, if and only if such $x, y$ can be chosen with in addition the coefficientwise reduction of $x$ equal to $0$.
--
--   This is the Gauss valuation attached to the discrete valuation subring $A_0 \subseteq L$, realised on the fraction field of $A_0[[q]]$ inside $L((q))$, together with presentations of the valuation ring and of its maximal ideal by means of denominators with non-zero reduction. It is used in the construction of charts at the origin of the Tate curve, and is cited by the statements producing such origin charts at Tate points, at full level and in the $\Gamma_1$-refined form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_subfield_valuationSubring_laurentSeries_gauss_of_isDiscreteValuationRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_subfield_valuationSubring_laurentSeries_gauss_of_isDiscreteValuationRing
    (L : Type) [Field L] (A₀ : ValuationSubring L) (hdvr : IsDiscreteValuationRing ↥A₀) :
    ∃ (L₂ : Subfield (LaurentSeries L)) (W₂ : ValuationSubring ↥L₂),

      (∀ f : LaurentSeries L, f ∈ L₂ ↔ ∃ x y : PowerSeries ↥A₀, y ≠ 0 ∧
        f * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L))) ∧

      (∀ f : ↥L₂, f ∈ W₂ ↔ ∃ x y : PowerSeries ↥A₀, y.map (IsLocalRing.residue ↥A₀) ≠ 0 ∧
        ((f : ↥L₂) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) =
          HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L))) ∧

      (∀ f : ↥L₂, f ∈ W₂.nonunits ↔ ∃ x y : PowerSeries ↥A₀, y.map (IsLocalRing.residue ↥A₀) ≠ 0 ∧
        x.map (IsLocalRing.residue ↥A₀) = 0 ∧
        ((f : ↥L₂) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap ↥A₀ L)) =
          HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap ↥A₀ L))) := by sorry
