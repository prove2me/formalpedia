-- Prove2me | Theorems.Thm_John_smul_mem_feasible_of_le_on_sphere
-- name    : John.smul_mem_feasible_of_le_on_sphere
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:23:14.215981+00:00
-- url     : https://prove2.me/theorems/76b7bd0a-5f96-4cf8-802d-0cb94cee2dfb
-- title:
--   John: smul mem feasible of le on sphere
-- statement:
--   **Rescaling to feasibility.** If `q (T u) ≤ s` for every unit vector `u` (with
--   `s > 0`), then `s⁻¹ • T` is feasible for `q`: by homogeneity, `q (T x) ≤ s ‖x‖` for
--   every `x`. Part of the John's-ellipsoid perturbation argument.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L533-L558
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L533-L558

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

theorem John.smul_mem_feasible_of_le_on_sphere {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))}
    {T : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)} {s : ℝ} (hs : 0 < s)
    (hT : ∀ u, ‖u‖ = 1 → q (T u) ≤ s) : ((s⁻¹ : ℝ) : 𝕜) • T ∈ Feasible q := by sorry
