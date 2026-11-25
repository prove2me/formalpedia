-- Prove2me | Theorems.Thm_John_exists_projection
-- name    : John.exists_projection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:24:23.037316+00:00
-- url     : https://prove2.me/theorems/0b753127-cd98-4aca-bbb8-2b64da726320
-- title:
--   John: exists projection
-- statement:
--   **Kadets–Snobar.** Every finite-dimensional subspace `V` of a normed
--   `𝕜`-space `Y` is the range of a bounded projection `P : Y →L[𝕜] Y` with
--   `‖P‖ ≤ √(dim V)`.
--
--   The proof puts `V` in John position: transport the Euclidean structure of
--   `𝕜^{dim V}` to `V` through the maximal-volume ellipsoid `M` (built from the John
--   decomposition of identity `∑ᵢ cᵢ uᵢ⊗uᵢ = id`). The contact points `uᵢ` give unit
--   vectors `vᵢ = M uᵢ ∈ V` and functionals `φᵢ = ⟪uᵢ, M⁻¹ ·⟫ ∈ V*` of norm `≤ 1`,
--   which Hahn–Banach (`exists_extension_norm_eq`) extends to `gᵢ ∈ Y*` without
--   increasing the norm. Then `P = ∑ᵢ cᵢ · gᵢ ⊗ vᵢ` is the identity on `V` (so it is
--   a projection onto `V`), and the weighted Cauchy–Schwarz estimate
--   `norm_sum_weight_smul_le` together with `∑ᵢ cᵢ = dim V` yields `‖P‖ ≤ √(dim V)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L954-L1051
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L954-L1051

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

theorem John.exists_projection {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (V : Submodule 𝕜 Y) [FiniteDimensional 𝕜 V] :
    ∃ P : Y →L[𝕜] Y, P.comp P = P ∧
      LinearMap.range (P : Y →ₗ[𝕜] Y) = V ∧ ‖P‖ ≤ Real.sqrt (Module.finrank 𝕜 V) := by sorry
