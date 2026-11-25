-- Prove2me | Theorems.Thm_GlobalTheory_CompletionAut_exists_natCast_valued_lt_one
-- name    : GlobalTheory.CompletionAut.exists_natCast_valued_lt_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:21:52.076907+00:00
-- url     : https://prove2.me/theorems/a9368925-49c5-4d99-b7f8-fccecc7d93c7
-- title:
--   Completion Aut: exists nat Cast valued lt one
-- statement:
--   The Completion Aut construction uses the exists nat Cast valued lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RingEquivAdicCompletionMemIntegersIff.lean#L10-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RingEquivAdicCompletionMemIntegersIff.lean#L10-L21

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

theorem GlobalTheory.CompletionAut.exists_natCast_valued_lt_one :
    ∃ p : ℕ, (p : v.adicCompletion F) ≠ 0 ∧ Valued.v (p : v.adicCompletion F) < 1 := by sorry
