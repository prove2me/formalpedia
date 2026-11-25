-- Prove2me | Theorems.Thm_GlobalTheory_CompletionAut_mem_of_pow_eq
-- name    : GlobalTheory.CompletionAut.mem_of_pow_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:21:32.405982+00:00
-- url     : https://prove2.me/theorems/af33acc2-a05c-5702-9073-880ac7345215
-- title:
--   Completion Aut: mem of pow eq
-- statement:
--   The Completion Aut construction uses the mem of pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RingEquivAdicCompletionMemIntegersIff.lean#L53-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RingEquivAdicCompletionMemIntegersIff.lean#L53-L87

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

theorem GlobalTheory.CompletionAut.mem_of_pow_eq {p e : ℕ} (he : 0 < e)
    (hp : Valued.v (p : v.adicCompletion F) = WithZero.exp (-(e : ℤ))) (hp0 : p ≠ 0)
    {x y : v.adicCompletion F} (h : y ^ (p * e + 1) = 1 + p * x ^ (p * e + 1)) :
    x ∈ v.adicCompletionIntegers F := by sorry
