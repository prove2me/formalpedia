-- Prove2me | Theorems.Thm_John_exists_projection_ker
-- name    : John.exists_projection_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:24:16.848804+00:00
-- url     : https://prove2.me/theorems/b7fab308-9b41-4c17-be00-c8d5c1e10e71
-- title:
--   John: exists projection ker
-- statement:
--   **Garling–Gordon, ε-form.** Every closed subspace `M` of a normed `𝕜`-space
--   `X` with finite-dimensional quotient is the kernel of a bounded projection
--   `P : X →L[𝕜] X` with `‖P‖ ≤ √(codim M) + ε`, for every `ε > 0`.
--
--   This is the dual of `exists_projection`, run in the finite-dimensional dual
--   `D = (X ⧸ M)*` (so no dual of `X` is needed). John position of the unit ball of
--   `D` gives contact points `uᵢ` and weights `cᵢ` with `∑ᵢ cᵢ = codim M`; the
--   `uᵢ` become unit functionals `fᵢ = Φ uᵢ ∈ D` on the quotient, and the contact
--   supports become norm-`≤ 1` functionals on `D`, that is, since `X ⧸ M` is
--   finite-dimensional, hence isometrically reflexive
--   (`NormedSpace.inclusionInDoubleDualLi`), vectors `wᵢ ∈ X ⧸ M` with `‖wᵢ‖ ≤ 1`.
--   Lifting each `wᵢ` to a representative `xᵢ ∈ X` with `‖xᵢ‖ < 1 + ε'`
--   (`Submodule.Quotient.norm_mk_lt`: the quotient norm is an infimum; this is the
--   sole source of the `ε`), the operator `P y = ∑ᵢ cᵢ · fᵢ(π y) · xᵢ` satisfies
--   `π ∘ P = π` (via the decomposition of identity and the Riesz representation on
--   the Euclidean model), hence is a projection with kernel `M`; Cauchy–Schwarz and
--   the quadratic identity `sum_weight_inner_sq` give `‖P‖ ≤ (1 + ε')·√(codim M)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L1210-L1338
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L1210-L1338

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

theorem John.exists_projection_ker {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (M : Submodule 𝕜 X) [IsClosed (M : Set X)] [FiniteDimensional 𝕜 (X ⧸ M)]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : X →L[𝕜] X, P.comp P = P ∧ LinearMap.ker (P : X →ₗ[𝕜] X) = M ∧
      ‖P‖ ≤ Real.sqrt (Module.finrank 𝕜 (X ⧸ M)) + ε := by sorry
