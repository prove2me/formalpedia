-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_spectrum_subset_range_ofReal
-- name    : GroundTheory.Automorphic.CompactSelfAdjoint.spectrum_subset_range_ofReal
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:11.847228+00:00
-- url     : https://prove2.me/theorems/aeccff82-cd0d-4bf5-bf6d-15e84e545d44
-- title:
--   Compact Self Adjoint: spectrum subset range of Real
-- statement:
--   The Compact Self Adjoint construction uses the spectrum subset range of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L167-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L167-L173

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

theorem GroundTheory.Automorphic.CompactSelfAdjoint.spectrum_subset_range_ofReal (hT : IsCompactOperator T) (hT' : IsSelfAdjoint T) :
    spectrum 𝕜 T ⊆ Set.range ((↑) : ℝ → 𝕜) := by sorry
