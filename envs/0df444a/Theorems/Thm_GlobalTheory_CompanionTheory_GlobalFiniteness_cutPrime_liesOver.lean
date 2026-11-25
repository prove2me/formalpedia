-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GlobalFiniteness_cutPrime_liesOver
-- name    : GlobalTheory.CompanionTheory.GlobalFiniteness.cutPrime_liesOver
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:51:04.422004+00:00
-- url     : https://prove2.me/theorems/7aed3e31-5872-58ad-93a8-c50eb52c69ce
-- title:
--   Global Finiteness: cut Prime lies Over
-- statement:
--   The Global Finiteness construction uses the cut Prime lies Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/NormalSubgroupLeUnramifiedFixing.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/NormalSubgroupLeUnramifiedFixing.lean#L35-L40

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

theorem GlobalTheory.CompanionTheory.GlobalFiniteness.cutPrime_liesOver {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A v) (M : IntermediateField F Ω) : (cutPrime A M).LiesOver v.asIdeal := by sorry
