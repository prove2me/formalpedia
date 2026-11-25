-- Prove2me | Theorems.Thm_John_no_neg_direction_of_maxVolume
-- name    : John.no_neg_direction_of_maxVolume
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:23:53.430912+00:00
-- url     : https://prove2.me/theorems/9ea54408-e206-4212-8361-423c8af9f6f8
-- title:
--   John: no neg direction of max Volume
-- statement:
--   **First-order optimality in John position.** If the identity has maximal `‖det‖`
--   among feasible operators for `q` (with `q ≤ ‖·‖`), then no self-adjoint trace-zero `H`
--   can satisfy `re ⟪u, H u⟫ ≤ -δ < 0` at every unit vector `u` touching the body
--   (`q u = 1`).
--
--   Otherwise `S = (1 - ρ)⁻¹ • (id + t H)` with `ρ = tδ/4` would be feasible for small
--   `t > 0`: near the touching set the Euclidean norm of `(id + t H) u` shrinks linearly in
--   `t` (`norm_add_smul_le_of_inner_le`; this is where `re ⟪u, H u⟫ ≤ -δ` enters), and
--   away from it `q` is uniformly below `1` by compactness
--   (`exists_gap_of_lt_one_on_compact`), so `S` is feasible by rescaling
--   (`smul_mem_feasible_of_le_on_sphere`). Meanwhile the trace-zero determinant bound
--   `one_sub_le_norm_det_one_add_smul` shows the perturbation loses only `O(t²)` of
--   determinant, which the first-order gain `(1 - ρ)⁻¹ ≥ 1 + tδ/4` beats. So `‖det S‖ > 1`,
--   contradicting maximality.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L688-L823
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/John.lean#L688-L823

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
set_option maxHeartbeats 400000

theorem John.no_neg_direction_of_maxVolume (hk : 0 < k)
    {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))} (hqc : Continuous q)
    (hq1 : ∀ x, q x ≤ ‖x‖) (hmax : ∀ S ∈ Feasible q, ‖S.det‖ ≤ 1)
    {H : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)}
    (hHsa : IsSelfAdjoint H)
    (htr : LinearMap.trace 𝕜 (EuclideanSpace 𝕜 (Fin k))
      (H : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hneg : ∀ u, ‖u‖ = 1 → q u = 1 → re ⟪u, H u⟫_𝕜 ≤ -δ) : False := by sorry
