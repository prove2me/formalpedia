-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_SplitPlace_two_primes
-- name    : GlobalTheory.CMVal.Euler.SplitPlace.two_primes
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:04:54.627714+00:00
-- url     : https://prove2.me/theorems/92184451-6009-4349-bf2e-729102e2036d
-- title:
--   Split Place: two primes
-- statement:
--   The Split Place construction uses the two primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplitsInCMFieldTwoPrimesDegreeOne.lean#L10-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplitsInCMFieldTwoPrimesDegreeOne.lean#L10-L37

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitsInCMFieldTwoPrimesDegreeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler GlobalTheory.CMVal.Euler.SplitPlace

theorem GlobalTheory.CMVal.Euler.SplitPlace.two_primes (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (p : Ideal (𝓞 F)) [p.IsMaximal] (P P' : p.primesOver (𝓞 E)) (hne : P ≠ P') :
    (∀ R : p.primesOver (𝓞 E), R = P ∨ R = P') ∧
      ∀ R : p.primesOver (𝓞 E), R.1.ramificationIdx (𝓞 F) * R.1.inertiaDeg (𝓞 F) = 1 := by sorry
