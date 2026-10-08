-- Prove2me | Theorems.Thm_OAI_StructuralCrouzeixReference_challenge
-- name    : OAI.StructuralCrouzeixReference.challenge
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:27.152506+00:00
-- url     : https://prove2.me/theorems/a02ab6cd-7c12-481f-834d-cc950c88a53b
-- statement:
--   The theorem states a conjunction of two claims. First, StructuralCrouzeix.FullEndpoint holds: for every admissible set U ⊂ ℂ (admissible meaning open, bounded, nonempty, convex over ℝ, with boundary homeomorphic to the circle, and such that at every boundary point p there is a local analytic chart χ with χ(0)=p, χ′(0)≠0 and, near 0, χ(z) lies on the boundary exactly when z is real), the following hold. For every a in U there exists a disk coordinate: an open set containing the closure of U and an analytic, injective, noncritical map toDisk on it with open image and analytic inverse fromDisk, whose image contains the closed unit disk, sends U onto the open unit disk, and sends a to 0. There also exists an exterior coordinate: a radius R>1 and a map t ↦ a₀t+b+h(1/t), with a₀≠0 and h analytic on the ball of radius R, which is injective and noncritical on |t|>1/R, sends the unit circle onto the boundary of U, sends points of |t|>1/R into U exactly when |t|<1, and sends points with |t|>1 outside the closure of U. Moreover, for any a in U, any disk coordinate f, any exterior coordinate G, any n>0 and any n×n complex matrix A whose numerical range lies in U, setting T = f(A) (the analytic functional calculus of toDisk applied to A), T is strictly feasible, meaning some Hermitian H and real τ satisfy H−1, τ−H and H−T*HT all positive definite. Furthermore there is κ with 1≤κ≤2 such that a minimizer H exists for τ=κ² (H with 1≤H≤τ and T*HT≤H, where τ is least possible), and for every such minimizer, with S the positive square root of H, A′=SAS⁻¹ and D=STS⁻¹, we have H positive definite, S invertible, D=f(A′), D*D≤1, spectral radius of D below 1, ‖S‖‖S⁻¹‖=κ, and κ≤‖R‖‖R⁻¹‖ for every invertible R with (RTR⁻¹)*(RTR⁻¹)≤1. Also there is a continuous positive-semidefinite-matrix-valued function Λ on the circle ℝ/ℤ with Haar integral equal to the identity, such that for every m>0 and every v analytic near the closure of U with values in m×m matrices, the analytic calculus of v at A′ equals the Haar integral of Λ(t)⊗v(boundary point at t), and the analytic calculus of v at A has norm at most κ times the supremum of ‖v(z)‖ over the closure of U. Second, the open unit disk in ℂ is admissible. The statement is formal and is currently admitted without proof.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/StructuralCrouzeix.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/StructuralCrouzeix.lean; bytes 7842..8052
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_StructuralCrouzeix

namespace OAI

universe u_61 u_63 u_67 u_83 u_84 u_181

namespace StructuralCrouzeixReference

/-- Intrinsic structural representation and admissibility of the unit disk. -/
theorem challenge : StructuralCrouzeix.FullEndpoint ∧
    StructuralCrouzeix.IsAdmissible (Metric.ball (0 : ℂ) 1) := by
  sorry

end StructuralCrouzeixReference
end OAI
