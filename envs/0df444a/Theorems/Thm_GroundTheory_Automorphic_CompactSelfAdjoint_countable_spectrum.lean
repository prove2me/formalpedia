-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_countable_spectrum
-- name    : GroundTheory.Automorphic.CompactSelfAdjoint.countable_spectrum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:52:46.083368+00:00
-- url     : https://prove2.me/theorems/3b8c13c3-9ba7-58db-9cce-12c3e63a3323
-- title:
--   Compact Self Adjoint: countable spectrum
-- statement:
--   The Compact Self Adjoint construction uses the countable spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L160-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L160-L165

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

theorem GroundTheory.Automorphic.CompactSelfAdjoint.countable_spectrum (hT : IsCompactOperator T) (hT' : IsSelfAdjoint T) :
    (spectrum 𝕜 T).Countable := by sorry
