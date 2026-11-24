-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_SplitPair_eq_exp_of_le
-- name    : GlobalTheory.CMVal.Euler.SplitPair.eq_exp_of_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:13.221744+00:00
-- url     : https://prove2.me/theorems/eef5eeb2-7088-4fad-897b-f08e1b3d3866
-- title:
--   Split Pair: eq exp of le
-- statement:
--   The Split Pair construction uses the eq exp of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeCharUnramifiedInverseSplitPair.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeCharUnramifiedInverseSplitPair.lean#L15-L19

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitsInCMFieldTwoPrimesDegreeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeCharUnramifiedInverseSplitPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler GlobalTheory.CMVal.Euler.SplitPair
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.Euler.SplitPair.eq_exp_of_le {x : WithZero (Multiplicative ℤ)} {m : ℤ} (h : x ≤ WithZero.exp m) (h' : ¬ x ≤ WithZero.exp (m - 1)) :
    x = WithZero.exp m := by sorry
