-- Prove2me | Theorems.Thm_GlobalTheory_ringEquiv_adicCompletion_mem_integers_iff
-- name    : GlobalTheory.ringEquiv_adicCompletion_mem_integers_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:50:37.52782+00:00
-- url     : https://prove2.me/theorems/976ea325-2e1f-5429-9859-1c3259b3c50c
-- title:
--   Global Theory: ring Equiv adic Completion mem integers iff
-- statement:
--   The Global Theory construction uses the ring Equiv adic Completion mem integers iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RingEquivAdicCompletionMemIntegersIff.lean#L107-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RingEquivAdicCompletionMemIntegersIff.lean#L107-L112

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
open GlobalTheory

theorem GlobalTheory.ringEquiv_adicCompletion_mem_integers_iff (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (θ : v.adicCompletion F ≃+* v.adicCompletion F)
    (x : v.adicCompletion F) :
    θ x ∈ v.adicCompletionIntegers F ↔ x ∈ v.adicCompletionIntegers F := by sorry
