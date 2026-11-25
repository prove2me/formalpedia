-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_countable_eigenvalues
-- name    : GroundTheory.Automorphic.CompactSelfAdjoint.countable_eigenvalues
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:04.38498+00:00
-- url     : https://prove2.me/theorems/475941cd-ebe1-44f7-a70a-b0bb6a247e23
-- title:
--   Compact Self Adjoint: countable eigenvalues
-- statement:
--   The Compact Self Adjoint construction uses the countable eigenvalues property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L139-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L139-L149

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

theorem GroundTheory.Automorphic.CompactSelfAdjoint.countable_eigenvalues (hT : IsCompactOperator T) (hT' : IsSelfAdjoint T) :
    {μ : 𝕜 | HasEigenvalue (T : E →ₗ[𝕜] E) μ}.Countable := by sorry
