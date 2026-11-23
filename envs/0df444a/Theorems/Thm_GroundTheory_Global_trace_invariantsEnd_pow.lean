-- Prove2me | Theorems.Thm_GroundTheory_Global_trace_invariantsEnd_pow
-- name    : GroundTheory.Global.trace_invariantsEnd_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:48.107375+00:00
-- url     : https://prove2.me/theorems/926b6f01-ea89-449a-a782-4e3ffc5f5a61
-- title:
--   Global: trace invariants End pow
-- statement:
--   The Global construction uses the trace invariants End pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L188-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L188-L194

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

theorem GroundTheory.Global.trace_invariantsEnd_pow (I : Subgroup G) (g : G) (hg : ∀ i ∈ I, g⁻¹ * i * g ∈ I)
    (m : ℕ) :
    LinearMap.trace ℂ _ (invariantsEnd ρ I g hg ^ m) = cosetAverage I ρ.character (g ^ m) := by sorry
