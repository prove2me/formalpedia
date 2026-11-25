-- Prove2me | Theorems.Thm_John_john_decomposition
-- name    : John.john_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:45:12.41978+00:00
-- url     : https://prove2.me/theorems/f4145131-38be-48ea-9be0-093d5ccf13a0
-- title:
--   John: john decomposition
-- statement:
--   **John decomposition of identity**, the classical core of John's ellipsoid
--   theorem.
--
--   In John position, that is, when the identity is a maximal-volume feasible operator for
--   the body seminorm `q` (`q u ≤ ‖u‖`, and `‖det S‖ ≤ 1` for every feasible `S`), the
--   identity is a positive combination of the rank-one projections onto contact
--   points, with weights summing to the dimension `k`:
--   `∑ᵢ ((cᵢ:𝕜) · ⟪uᵢ, x⟫) • uᵢ = x`, with `uᵢ ∈ Contact q`, `cᵢ ≥ 0`, `∑ᵢ cᵢ = k`.
--
--   Proof: `k⁻¹ • id` lies in the convex hull of `{u ⊗ u : u ∈ Contact q}`; otherwise
--   `exists_selfAdjoint_of_not_mem_convexHull` would produce a self-adjoint trace-zero
--   improving direction, which `no_neg_direction_of_maxVolume` forbids (all unit vectors
--   with `q u = 1` are contact points by `mem_contact_of_apply_eq_one`). Carathéodory
--   (`mem_convexHull_iff_exists_fintype`) turns hull membership into a finite convex
--   combination `∑ᵢ wᵢ (uᵢ ⊗ uᵢ) = k⁻¹ • id`; multiplying by `k` and evaluating at `x`
--   gives the decomposition with `cᵢ = k wᵢ`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L841-L892
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L841-L892

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
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped InnerProductSpace ComplexConjugate
open RCLike (re)
open John
variable {𝕜 : Type u} [RCLike 𝕜] {k : ℕ}

theorem John.john_decomposition (q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k)))
    (hq : Continuous q) (hq1 : ∀ u, q u ≤ ‖u‖)
    (hmax : ∀ S ∈ Feasible q, ‖S.det‖ ≤ 1) :
    ∃ (N : ℕ) (u : Fin N → EuclideanSpace 𝕜 (Fin k)) (c : Fin N → ℝ),
      (∀ i, u i ∈ Contact q) ∧ (∀ i, 0 ≤ c i) ∧ (∑ i, c i = (k : ℝ)) ∧
      (∀ x, ∑ i, ((c i : 𝕜) * ⟪u i, x⟫_𝕜) • u i = x) := by sorry
