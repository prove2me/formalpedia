-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_finite_eigenvalues_norm_ge
-- name    : GroundTheory.Automorphic.CompactSelfAdjoint.finite_eigenvalues_norm_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:27.123216+00:00
-- url     : https://prove2.me/theorems/02efd0f1-56c4-411d-8aa3-99a6584f191b
-- title:
--   Compact Self Adjoint: finite eigenvalues norm ge
-- statement:
--   The Compact Self Adjoint construction uses the finite eigenvalues norm ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L98-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L98-L137

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CompactSelfAdjoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.CompactSelfAdjoint
open Module End Submodule Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y
variable {T : E →L[𝕜] E}
variable [CompleteSpace E]

theorem GroundTheory.Automorphic.CompactSelfAdjoint.finite_eigenvalues_norm_ge (hT : IsCompactOperator T) (hT' : IsSelfAdjoint T) {ε : ℝ}
    (hε : 0 < ε) : {μ : 𝕜 | HasEigenvalue (T : E →ₗ[𝕜] E) μ ∧ ε ≤ ‖μ‖}.Finite := by sorry
