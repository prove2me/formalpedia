-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_hasEigenvalue_of_mem_spectrum
-- name    : GroundTheory.Automorphic.CompactSelfAdjoint.hasEigenvalue_of_mem_spectrum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:33.085043+00:00
-- url     : https://prove2.me/theorems/e9a359df-0c62-453e-a6b3-fa2e9183d868
-- title:
--   Compact Self Adjoint: has Eigenvalue of mem spectrum
-- statement:
--   The Compact Self Adjoint construction uses the has Eigenvalue of mem spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L151-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L151-L153

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

theorem GroundTheory.Automorphic.CompactSelfAdjoint.hasEigenvalue_of_mem_spectrum (hT : IsCompactOperator T) {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 T) (h0 : μ ≠ 0) : HasEigenvalue (T : E →ₗ[𝕜] E) μ := by sorry
