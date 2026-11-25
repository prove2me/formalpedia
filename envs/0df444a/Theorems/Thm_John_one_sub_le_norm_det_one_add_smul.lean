-- Prove2me | Theorems.Thm_John_one_sub_le_norm_det_one_add_smul
-- name    : John.one_sub_le_norm_det_one_add_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:23:51.417743+00:00
-- url     : https://prove2.me/theorems/535c96fc-00c2-4b87-80ac-88bcf5283032
-- title:
--   John: one sub le norm det one add smul
-- statement:
--   **Second-order determinant bound for a trace-zero perturbation.** For a
--   self-adjoint `H` with `tr H = 0` and `0 < t` with `t‖H‖ ≤ 1/2`,
--   `‖det (id + t • H)‖ ≥ 1 - 2t²·(k·‖H‖²)`.
--
--   In an orthonormal eigenbasis (spectral theorem for symmetric operators),
--   `det (id + tH) = ∏ᵢ (1 + tλᵢ)` with real eigenvalues `λᵢ` satisfying
--   `∑ᵢ λᵢ = tr H = 0` and `|λᵢ| ≤ ‖H‖`; the Weierstrass-type bound
--   `one_sub_two_mul_sum_sq_le_prod_one_add` then gives
--   `∏(1+tλᵢ) ≥ 1 - 2t²∑λᵢ² ≥ 1 - 2t²k‖H‖²`. The trace-zero hypothesis is what makes
--   the determinant loss second order in `t`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L599-L670
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L599-L670

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

theorem John.one_sub_le_norm_det_one_add_smul
    {H : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)}
    (hHsa : IsSelfAdjoint H)
    (htr : LinearMap.trace 𝕜 (EuclideanSpace 𝕜 (Fin k))
      (H : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) = 0)
    {t : ℝ} (ht0 : 0 < t) (htH : t * ‖H‖ ≤ 1 / 2) :
    1 - 2 * (t ^ 2 * ((k : ℝ) * ‖H‖ ^ 2))
      ≤ ‖(ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k))
          + ((t : ℝ) : 𝕜) • H).det‖ := by sorry
