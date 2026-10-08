-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affine_bernstein
-- name    : OAI.AffineBernstein.affine_bernstein
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:20.445056+00:00
-- url     : https://prove2.me/theorems/0f6368a8-3522-455d-b28e-6e5195399f56
-- statement:
--   The theorem states that, for every integer dimension 3 ≤ n ≤ 9, a nonempty open convex set Ω ⊆ ℝⁿ and a function u : ℝⁿ → ℝ that is smooth on Ω satisfy the following conclusion under three hypotheses. First, the Hessian H = D²u is positive definite at every point of Ω. Second, u satisfies the affine maximal equation ∑ᵢⱼ Uᵢⱼ ∂ᵢ∂ⱼw = 0 throughout Ω, where U = (det H)H⁻¹ and w = (det H)^{−(n+1)/(n+2)}. Third, the graph is complete for its intrinsic Euclidean path distance: the distance between x and y in Ω is the infimum over C¹ paths γ in Ω joining them of ∫₀¹ √(‖γ′(t)‖² + (Du(γ(t))γ′(t))²) dt, and every Cauchy sequence for this distance has a limit in Ω for the same distance. Then Ω = ℝⁿ and there exist a symmetric positive definite real n × n matrix A, a vector b ∈ ℝⁿ, and c ∈ ℝ such that u(x) = ½xᵀAx + b·x + c for every x ∈ ℝⁿ. Moreover, an invertible affine map of ℝⁿ × ℝ carries the standard paraboloid {(x, ‖x‖²)} onto the graph {(x, u(x)) : x ∈ Ω}.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/AffineBernstein.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/AffineBernstein.lean; bytes 3217..4030
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_AffineBernstein

namespace OAI

noncomputable section

open Set MeasureTheory

open scoped BigOperators ContDiff ENNReal

namespace AffineBernstein

/-- Literal main theorem, with its stated affine-image consequence. -/
theorem affine_bernstein
    (n : ℕ) (hn₃ : 3 ≤ n) (hn₉ : n ≤ 9)
    (Ω : Set (Space n)) (hΩne : Ω.Nonempty) (hΩopen : IsOpen Ω)
    (hΩconvex : Convex ℝ Ω) (u : Space n → ℝ)
    (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hmax : AffineMaximalOn Ω u)
    (hcomplete : EuclideanGraphComplete Ω u) :
    Ω = univ ∧
      (∃ (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) (c : ℝ),
        A.IsSymm ∧ A.PosDef ∧
        ∀ x, u x = (1 / 2 : ℝ) * (∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j)
          + (∑ i : Fin n, b i * x i) + c) ∧
      (∃ e : (Space n × ℝ) ≃ᵃ[ℝ] (Space n × ℝ),
        e '' standardParaboloid n = graph Ω u) := by
  sorry

end AffineBernstein
end
end OAI
