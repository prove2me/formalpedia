-- Prove2me | Theorems.Thm_John_norm_add_smul_le_of_inner_le
-- name    : John.norm_add_smul_le_of_inner_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:23:41.171572+00:00
-- url     : https://prove2.me/theorems/b963106d-166c-4ef6-888f-a46c4d1baef4
-- title:
--   John: norm add smul le of inner le
-- statement:
--   **Linear norm shrinking near the touching set.** If `re ⟪u, H u⟫ ≤ -(δ/2)` at a
--   unit vector `u`, then `‖u + t • H u‖ ≤ 1 - tδ/4` for `0 < t` with `t‖H‖² ≤ δ/2` and
--   `tδ ≤ 4`: expanding the square,
--   `‖u + tHu‖² ≤ 1 - tδ + t²‖H‖² ≤ 1 - tδ/2 ≤ (1 - tδ/4)²`.
--   This is the first-order feasibility gain of the John perturbation.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L565-L587
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L565-L587

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

theorem John.norm_add_smul_le_of_inner_le
    {H : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)}
    {u : EuclideanSpace 𝕜 (Fin k)} (hu : ‖u‖ = 1) {t δ : ℝ} (ht0 : 0 < t)
    (h1 : t * ‖H‖ ^ 2 ≤ δ / 2) (h2 : t * δ ≤ 4)
    (hA : re ⟪u, H u⟫_𝕜 ≤ -(δ / 2)) :
    ‖u + ((t : ℝ) : 𝕜) • H u‖ ≤ 1 - t * δ / 4 := by sorry
