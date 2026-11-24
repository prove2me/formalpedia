-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_isClosed_eigenspace
-- name    : GroundTheory.Automorphic.CompactSelfAdjoint.isClosed_eigenspace
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:44.131781+00:00
-- url     : https://prove2.me/theorems/dc3bbfab-a715-4d0d-8596-3e47b4ebdcc8
-- title:
--   Compact Self Adjoint: is Closed eigenspace
-- statement:
--   The Compact Self Adjoint construction uses the is Closed eigenspace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L21-L28

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

theorem GroundTheory.Automorphic.CompactSelfAdjoint.isClosed_eigenspace (T : E →L[𝕜] E) (μ : 𝕜) :
    IsClosed (eigenspace (T : E →ₗ[𝕜] E) μ : Set E) := by sorry
