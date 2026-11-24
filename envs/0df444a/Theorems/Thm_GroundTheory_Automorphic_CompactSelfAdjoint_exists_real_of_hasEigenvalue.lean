-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_exists_real_of_hasEigenvalue
-- name    : GroundTheory.Automorphic.CompactSelfAdjoint.exists_real_of_hasEigenvalue
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:08.392869+00:00
-- url     : https://prove2.me/theorems/04739352-655a-4e2e-9f83-006e6bf264fd
-- title:
--   Compact Self Adjoint: exists real of has Eigenvalue
-- statement:
--   The Compact Self Adjoint construction uses the exists real of has Eigenvalue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L93-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L93-L96

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

theorem GroundTheory.Automorphic.CompactSelfAdjoint.exists_real_of_hasEigenvalue (hT' : IsSelfAdjoint T) {μ : 𝕜}
    (hμ : HasEigenvalue (T : E →ₗ[𝕜] E) μ) : ∃ r : ℝ, μ = r := by sorry
