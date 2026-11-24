-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_SplitPair_loc_mul_loc
-- name    : GlobalTheory.CMVal.Euler.SplitPair.loc_mul_loc
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:06:00.105958+00:00
-- url     : https://prove2.me/theorems/d6a46d0c-7860-4b3f-b8c4-1d1d86fd667f
-- title:
--   Split Pair: loc mul loc
-- statement:
--   The Split Pair construction uses the loc mul loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeCharUnramifiedInverseSplitPair.lean#L47-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeCharUnramifiedInverseSplitPair.lean#L47-L61

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

theorem GlobalTheory.CMVal.Euler.SplitPair.loc_mul_loc {χ : HChar E} (hF : TrivOnF χ) {v : HeightOneSpectrum (OF E)} {P P' : HeightOneSpectrum (𝓞 E)}
    (hP : Over P v) (hP' : Over P' v) (hne : P ≠ P') (h2 : ∀ R, Over R v → R = P ∨ R = P') (a : OF E) (ha : a ≠ 0) :
    χ.loc P (locF P a ha) * χ.loc P' (locF P' a ha) = 1 := by sorry
