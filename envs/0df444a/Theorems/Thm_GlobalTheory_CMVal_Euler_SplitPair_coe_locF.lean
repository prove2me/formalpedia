-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_SplitPair_coe_locF
-- name    : GlobalTheory.CMVal.Euler.SplitPair.coe_locF
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:04.310259+00:00
-- url     : https://prove2.me/theorems/e9115bb1-2562-427d-81a9-e9f82be886ff
-- title:
--   Split Pair: coe loc F
-- statement:
--   The Split Pair construction uses the coe loc F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeCharUnramifiedInverseSplitPair.lean#L45-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeCharUnramifiedInverseSplitPair.lean#L45-L45

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

theorem GlobalTheory.CMVal.Euler.SplitPair.coe_locF (P : HeightOneSpectrum (𝓞 E)) (a : OF E) (ha : a ≠ 0) : (locF P a ha : P.adicCompletion E) = iota a P := by sorry
