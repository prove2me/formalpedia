-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GlobalFiniteness_mem_cutPrime_iff
-- name    : GlobalTheory.CompanionTheory.GlobalFiniteness.mem_cutPrime_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:29:12.317217+00:00
-- url     : https://prove2.me/theorems/3a051c61-d805-5f04-b3e4-faaafdd69072
-- title:
--   Global Finiteness: mem cut Prime iff
-- statement:
--   The Global Finiteness construction uses the mem cut Prime iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/NormalSubgroupLeUnramifiedFixing.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/NormalSubgroupLeUnramifiedFixing.lean#L30-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_NormalSubgroupLeUnramifiedFixing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GlobalFiniteness
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem GlobalTheory.CompanionTheory.GlobalFiniteness.mem_cutPrime_iff (A : ValuationSubring Ω) (M : IntermediateField F Ω) (z : 𝓞 M) :
    z ∈ cutPrime A M ↔ A.valuation ((z : M) : Ω) < 1 := by sorry
