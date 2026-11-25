-- Prove2me | Theorems.Thm_John_sum_weight_mul_le_sqrt
-- name    : John.sum_weight_mul_le_sqrt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:22:46.369396+00:00
-- url     : https://prove2.me/theorems/9c19cd2b-9ab3-4a3e-bbb5-f608c027d071
-- title:
--   John: sum weight mul le sqrt
-- statement:
--   **Weighted Cauchy–Schwarz.** For nonnegative weights `cᵢ`,
--   `∑ᵢ cᵢ tᵢ ≤ √(∑ᵢ cᵢ) · √(∑ᵢ cᵢ tᵢ²)`.
--
--   Cauchy–Schwarz applied to the vectors `(√cᵢ)` and `(√cᵢ · tᵢ)`. Paired with a
--   decomposition of identity (where `∑ᵢ cᵢ` is the dimension) this is what turns a
--   quadratic bound into the linear bound needed for a projection norm.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L313-L331
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L313-L331

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

theorem John.sum_weight_mul_le_sqrt {N : ℕ} (c : Fin N → ℝ) (hc : ∀ i, 0 ≤ c i) (t : Fin N → ℝ) :
    ∑ i, c i * t i ≤ Real.sqrt (∑ i, c i) * Real.sqrt (∑ i, c i * t i ^ 2) := by sorry
