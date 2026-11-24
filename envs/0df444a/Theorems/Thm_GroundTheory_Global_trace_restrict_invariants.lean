-- Prove2me | Theorems.Thm_GroundTheory_Global_trace_restrict_invariants
-- name    : GroundTheory.Global.trace_restrict_invariants
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:43:19.404803+00:00
-- url     : https://prove2.me/theorems/47246563-6cb6-494c-92b3-62c6a32a9e1e
-- title:
--   Global: trace restrict invariants
-- statement:
--   The Global construction uses the trace restrict invariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L146-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L146-L182

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField Polynomial
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)

theorem GroundTheory.Global.trace_restrict_invariants (I : Subgroup G) (B : Module.End ℂ V)
    (hB : ∀ x ∈ subgroupInvariants ρ I, B x ∈ subgroupInvariants ρ I) :
    LinearMap.trace ℂ _ (B.restrict hB) =
      (Nat.card I : ℂ)⁻¹ * ∑ᶠ i : I, LinearMap.trace ℂ V (B * ρ i) := by sorry
