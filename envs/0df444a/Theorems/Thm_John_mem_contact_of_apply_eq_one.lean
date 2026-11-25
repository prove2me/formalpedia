-- Prove2me | Theorems.Thm_John_mem_contact_of_apply_eq_one
-- name    : John.mem_contact_of_apply_eq_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:23:57.713867+00:00
-- url     : https://prove2.me/theorems/4d4efbde-728c-48c9-98d9-0c7418b1ff65
-- title:
--   John: mem contact of apply eq one
-- statement:
--   **Every touching point is a contact point.** If `q ≤ ‖·‖` and `u` is a unit vector
--   with `q u = 1`, then `u ∈ Contact q`. The supporting functional of `{q ≤ 1}` at `u`
--   produced by seminorm-Hahn–Banach (`Seminorm.exists_inner_le_of_apply`) is represented by
--   a vector `v` with `re ⟪u, v⟫ = 1` and `‖v‖ ≤ 1`; equality in Cauchy–Schwarz forces
--   `v = u`, so `u` itself supports the body.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L361-L379
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L361-L379

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

theorem John.mem_contact_of_apply_eq_one {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))}
    (hq1 : ∀ x, q x ≤ ‖x‖) {u : EuclideanSpace 𝕜 (Fin k)} (hu : ‖u‖ = 1) (hqu : q u = 1) :
    u ∈ Contact q := by sorry
