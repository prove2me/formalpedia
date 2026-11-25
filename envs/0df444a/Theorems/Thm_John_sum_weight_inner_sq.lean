-- Prove2me | Theorems.Thm_John_sum_weight_inner_sq
-- name    : John.sum_weight_inner_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:45:10.983104+00:00
-- url     : https://prove2.me/theorems/d274b2c3-dc8e-4c28-b7f5-5085b9ace1fb
-- title:
--   John: sum weight inner sq
-- statement:
--   **Quadratic form of a decomposition of identity.** If
--   `∑ᵢ ((cᵢ:𝕜) · ⟪uᵢ, x⟫) • uᵢ = x` for all `x`, then `∑ᵢ cᵢ · ‖⟪uᵢ, z⟫‖² = ‖z‖²`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L296-L305
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L296-L305

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

theorem John.sum_weight_inner_sq {N : ℕ} (c : Fin N → ℝ) (u : Fin N → EuclideanSpace 𝕜 (Fin k))
    (hdec : ∀ x, ∑ i, ((c i : 𝕜) * ⟪u i, x⟫_𝕜) • u i = x) (z : EuclideanSpace 𝕜 (Fin k)) :
    ∑ i, c i * ‖⟪u i, z⟫_𝕜‖ ^ 2 = ‖z‖ ^ 2 := by sorry
