-- Prove2me | Theorems.Thm_GlobalTheory_CompletionAut_map_mem
-- name    : GlobalTheory.CompletionAut.map_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:22:57.023013+00:00
-- url     : https://prove2.me/theorems/0cf9cbb0-d0f6-4137-83eb-3df2083bd683
-- title:
--   Completion Aut: map mem
-- statement:
--   The Completion Aut construction uses the map mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RingEquivAdicCompletionMemIntegersIff.lean#L89-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RingEquivAdicCompletionMemIntegersIff.lean#L89-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RingEquivAdicCompletionMemIntegersIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial
open GlobalTheory GlobalTheory.CompletionAut
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem GlobalTheory.CompletionAut.map_mem (θ : v.adicCompletion F →+* v.adicCompletion F) {x : v.adicCompletion F}
    (hx : x ∈ v.adicCompletionIntegers F) : θ x ∈ v.adicCompletionIntegers F := by sorry
