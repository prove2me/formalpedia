-- Prove2me | Theorems.Thm_John_norm_sum_weight_smul_le
-- name    : John.norm_sum_weight_smul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:24:04.44849+00:00
-- url     : https://prove2.me/theorems/dc294b1a-c777-4b88-a56f-c47812149941
-- title:
--   John: norm sum weight smul le
-- statement:
--   **Weighted Cauchy–Schwarz for a decomposition of identity** (the analytic
--   heart of the Kadets–Snobar estimate). If `∑ᵢ ((cᵢ:𝕜)·⟪uᵢ,x⟫)•uᵢ = x` and
--   `cᵢ ≥ 0`, then for any scalars `aᵢ`, `‖∑ᵢ ((cᵢ:𝕜)·aᵢ)•uᵢ‖ ≤ √(∑ᵢ cᵢ·‖aᵢ‖²)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L897-L940
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L897-L940

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

theorem John.norm_sum_weight_smul_le {N : ℕ} (c : Fin N → ℝ)
    (u : Fin N → EuclideanSpace 𝕜 (Fin k))
    (hdec : ∀ x, ∑ i, ((c i : 𝕜) * ⟪u i, x⟫_𝕜) • u i = x)
    (hc : ∀ i, 0 ≤ c i) (a : Fin N → 𝕜) :
    ‖∑ i, ((c i : 𝕜) * a i) • u i‖ ≤ Real.sqrt (∑ i, c i * ‖a i‖ ^ 2) := by sorry
