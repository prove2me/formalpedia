-- Prove2me | Theorems.Thm_John_norm_inner_le_of_contact
-- name    : John.norm_inner_le_of_contact
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:44:31.160398+00:00
-- url     : https://prove2.me/theorems/e104a0ea-9d92-41c9-9c1f-e5cedbe5bf05
-- title:
--   John: norm inner le of contact
-- statement:
--   **Contact support.** A contact point `u` has `‖⟪x, u⟫‖ ≤ q x` for all `x`:
--   choosing a unit phase `a` with `re ⟪a • x, u⟫ = ‖⟪x, u⟫‖`, the contact bound and
--   `𝕜`-homogeneity of `q` give the claim.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L278-L292
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L278-L292

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

theorem John.norm_inner_le_of_contact {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))}
    {u : EuclideanSpace 𝕜 (Fin k)} (hu : u ∈ Contact q) (x : EuclideanSpace 𝕜 (Fin k)) :
    ‖⟪x, u⟫_𝕜‖ ≤ q x := by sorry
