-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactSelfAdjoint_eventually_notMem_spectrum
-- name    : GroundTheory.Automorphic.CompactSelfAdjoint.eventually_notMem_spectrum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:52:55.588509+00:00
-- url     : https://prove2.me/theorems/614f9fe6-7ac4-4dac-8406-73e325e0cfe8
-- title:
--   Compact Self Adjoint: eventually not Mem spectrum
-- statement:
--   The Compact Self Adjoint construction uses the eventually not Mem spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L175-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CompactSelfAdjoint.lean#L175-L190

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

theorem GroundTheory.Automorphic.CompactSelfAdjoint.eventually_notMem_spectrum (hT : IsCompactOperator T) (hT' : IsSelfAdjoint T) {μ : 𝕜}
    (hμ : μ ≠ 0) : ∀ᶠ ν in 𝓝[≠] μ, ν ∉ spectrum 𝕜 T := by sorry
