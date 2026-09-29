-- Prove2me | Theorems.Thm_Kall1976_distribution_by_basis_regions
-- name    : Kall1976.distribution_by_basis_regions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T06:52:06.225203+00:00
-- url     : https://prove2.me/theorems/5e2a9449-855b-4d36-a746-bf8094b031a9
-- title:
--   Theorem 8: distribution by basis regions
-- statement:
--   Under Kall's Assumption A1, the ordered basis regions cover the random parameter space with total probability one, and the finite optimal-value distribution function equals the sum of the density integrals over basis regions whose basis value is at most the threshold.
-- source:
--   Peter Kall, Stochastic Linear Programming, Springer, 1976, Chapter II §1, Theorem 8, printed p. 29 / PDF35; affine model (5) printed p. 27 / PDF33; Assumption A1 printed p. 28 / PDF34; Theorem 4 assumptions printed p. 25 / PDF31. https://doi.org/10.1007/978-3-642-66252-2.

import Definitions.Def_Kall1976_Distribution

open MeasureTheory
open scoped ENNReal

namespace Kall1976

/-- Kall (1976), Chapter II §1 Theorem 8, printed p. 29 / PDF35.
A1 is expressed by a density, the two almost-sure implications of Theorem 4,
and one nonsingular column minor at a point of T. The enumeration contains
exactly the almost nonsingular bases, with columns in increasing order.
The density is ENNReal-valued; the nonnegative source integrals are lintegrals.
T is the measurable range carrying the probability law, extended to ambient
Euclidean space. No integrability of the optimal value is assumed. -/
theorem distribution_by_basis_regions
    {r m n q : ℕ} (D : AffineLP r m n)
    (T : Set (Fin r → ℝ)) (hT : MeasurableSet T)
    (μ : Measure (Fin r → ℝ)) [IsProbabilityMeasure μ]
    (f : (Fin r → ℝ) → ℝ≥0∞) (hf : Measurable f)
    (hdensity : μ = volume.withDensity f) (hsupport : ∀ᵐ t ∂μ, t ∈ T)
    (hA1b : ∀ᵐ t ∂μ,
      (∀ u : Fin m → ℝ,
        (∀ j, 0 ≤ Matrix.mulVec (D.A t).transpose u j) → 0 ≤ dotProduct (D.b t) u) ∧
      (∀ w : Fin n → ℝ, (∀ j, 0 ≤ w j) →
        Matrix.mulVec (D.A t) w = 0 → 0 ≤ dotProduct (D.c t) w))
    (hA1c : ∃ t ∈ T, ∃ τ : Fin m → Fin n,
      StrictMono τ ∧ (basisMatrix D τ t).det ≠ 0)
    (σ : Fin q → Fin m → Fin n) (hunique : Function.Injective σ)
    (henumeration : ∀ τ : Fin m → Fin n,
      (∃ i, σ i = τ) ↔ StrictMono τ ∧ ∃ t ∈ T, (basisMatrix D τ t).det ≠ 0) :
    μ (⋃ i, basisRegion D T σ i) = ∑ i, μ (basisRegion D T σ i) ∧
    (∑ i, μ (basisRegion D T σ i)) = 1 ∧
    (∀ ξ : ℝ,
      μ {t | t ∈ T ∧
        (⊥ : EReal) < KallMayer.Recourse.LPValue (D.A t) (D.c t) (D.b t) ∧
        KallMayer.Recourse.LPValue (D.A t) (D.c t) (D.b t) ≤ (ξ : EReal)} =
      ∑ i, ∫⁻ t in {t | t ∈ basisRegion D T σ i ∧ basisValue D (σ i) t ≤ ξ},
        f t ∂volume) := by sorry

end Kall1976
