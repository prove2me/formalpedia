-- Prove2me | Theorems.Thm_GlobalTheory_RegularAscent_isRegularLocalRing_of_quotient_prime
-- name    : GlobalTheory.RegularAscent.isRegularLocalRing_of_quotient_prime
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:20:30.487162+00:00
-- url     : https://prove2.me/theorems/9390f095-7e80-458f-ba01-3a631961db74
-- title:
--   Regular Ascent: is Regular Local Ring of quotient prime
-- statement:
--   The Regular Ascent construction uses the is Regular Local Ring of quotient prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRegularLocalRingOfRegularQuotient.lean#L52-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRegularLocalRingOfRegularQuotient.lean#L52-L69

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRegularLocalRingOfRegularQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.RegularAscent

theorem GlobalTheory.RegularAscent.isRegularLocalRing_of_quotient_prime :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
      (r : ℕ) (f : Fin r → R), p = Ideal.span (Set.range f) → p.height = r →
      IsRegularLocalRing (R ⧸ p) → IsRegularLocalRing R := by sorry
