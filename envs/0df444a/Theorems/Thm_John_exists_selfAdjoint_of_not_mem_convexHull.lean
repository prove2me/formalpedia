-- Prove2me | Theorems.Thm_John_exists_selfAdjoint_of_not_mem_convexHull
-- name    : John.exists_selfAdjoint_of_not_mem_convexHull
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:08:11.43108+00:00
-- url     : https://prove2.me/theorems/5dbe120c-578e-4f4e-91c1-53e87801a41b
-- title:
--   John: exists self Adjoint of not mem convex Hull
-- statement:
--   **The separation step of John's theorem.** If, in John position, `k⁻¹ • id` is not a
--   convex combination of contact projections `u ⊗ u`, then some self-adjoint trace-zero
--   direction `H` improves all contact points at once: `re ⟪u, H u⟫ ≤ -δ < 0` on `Contact q`.
--
--   Proof: the contact set is compact, so the set of its rank-one projections is compact and
--   (in finite dimensions) its convex hull is compact, hence closed; geometric Hahn–Banach
--   (`RCLike.geometric_hahn_banach_closed_point`) separates `k⁻¹ • id` from it. Trace duality
--   (`ContinuousLinearMap.exists_trace_repr`) writes the separating functional as
--   `A ↦ tr (A ∘ G)`; on rank-one projections this evaluates to `re ⟪u, G u⟫`
--   (`trace_rankOneSA_comp`). Passing to the self-adjoint part of `G` and subtracting the
--   right multiple of the identity makes the trace zero without changing the inequality.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L419-L513
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L419-L513

module
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_CompactConvexHull
public import Definitions.Def_BasicResults_JohnIngredients
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Seminorm
public import Mathlib.Topology.Order.Compact
public import Definitions.Def_BasicResults_John
public import Theorems.Thm_IsCompact_convexHull

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped InnerProductSpace ComplexConjugate
open RCLike (re)
open John
variable {𝕜 : Type u} [RCLike 𝕜] {k : ℕ}

theorem John.exists_selfAdjoint_of_not_mem_convexHull (hk : 0 < k)
    {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))}
    (hmem : ((k : ℝ)⁻¹ • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)))
      ∉ convexHull ℝ (rankOneSA '' Contact q)) :
    ∃ (H : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)) (δ : ℝ), 0 < δ ∧
      IsSelfAdjoint H ∧
      LinearMap.trace 𝕜 (EuclideanSpace 𝕜 (Fin k))
        (H : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) = 0 ∧
      ∀ u ∈ Contact q, re ⟪u, H u⟫_𝕜 ≤ -δ := by sorry
