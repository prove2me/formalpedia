-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_orthogonal_iSup_iInf_eigenspaces_eq_bot
-- name    : GroundTheory.Automorphic.CompactSelfAdjoint.orthogonal_iSup_iInf_eigenspaces_eq_bot
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:28:40.776799+00:00
-- url     : https://prove2.me/theorems/2c589a3b-793b-41c3-8cf4-6645602606e9
-- title:
--   Compact Self Adjoint: orthogonal i Sup i Inf eigenspaces eq bot
-- statement:
--   The Compact Self Adjoint construction uses the orthogonal i Sup i Inf eigenspaces eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L245-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L245-L337

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
variable [CompleteSpace E]

theorem GroundTheory.Automorphic.CompactSelfAdjoint.orthogonal_iSup_iInf_eigenspaces_eq_bot {ι : Type*} (T : ι → E →L[𝕜] E)
    (hT : ∀ i, IsCompactOperator (T i)) (hS : ∀ i, (T i : E →ₗ[𝕜] E).IsSymmetric)
    (hC : ∀ i j, Commute (T i) (T j)) :
    (⨆ χ : ι → 𝕜, ⨅ i, eigenspace (T i : E →ₗ[𝕜] E) (χ i))ᗮ = ⊥ := by sorry
