-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_eq_exp_neg_one_of_le_of_not_le
-- name    : GlobalTheory.CMVal.Euler.eq_exp_neg_one_of_le_of_not_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:06:47.63296+00:00
-- url     : https://prove2.me/theorems/bbdd1ef4-c2eb-4d02-8baf-1b4d7be3806c
-- title:
--   Euler: eq exp neg one of le of not le
-- statement:
--   The Euler construction uses the eq exp neg one of le of not le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniformiserSplitPlaceCmOrderNonunit.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniformiserSplitPlaceCmOrderNonunit.lean#L25-L31

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitsInCMFieldTwoPrimesDegreeOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniformiserSplitPlaceCmOrderNonunit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler

theorem GlobalTheory.CMVal.Euler.eq_exp_neg_one_of_le_of_not_le {g : WithZero (Multiplicative ℤ)} (h1 : g ≤ WithZero.exp (-1 : ℤ))
    (h2 : ¬ g ≤ WithZero.exp (-2 : ℤ)) : g = WithZero.exp (-1 : ℤ) := by sorry
