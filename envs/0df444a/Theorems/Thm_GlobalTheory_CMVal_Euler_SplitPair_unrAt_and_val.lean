-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_SplitPair_unrAt_and_val
-- name    : GlobalTheory.CMVal.Euler.SplitPair.unrAt_and_val
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:25.983824+00:00
-- url     : https://prove2.me/theorems/b60fa0b5-87e8-4c8e-9511-af4f6829028d
-- title:
--   Split Pair: unr At and val
-- statement:
--   The Split Pair construction uses the unr At and val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeCharUnramifiedInverseSplitPair.lean#L63-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeCharUnramifiedInverseSplitPair.lean#L63-L113

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

theorem GlobalTheory.CMVal.Euler.SplitPair.unrAt_and_val : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar E) (v : HeightOneSpectrum (OF E))
    (P P' : HeightOneSpectrum (𝓞 E)), TrivOnF χ → Splits v → Over P v → Over P' v → P ≠ P' → LevelLe χ P' 1 → UnrAt χ P →
    UnrAt χ P' ∧ val χ P' = (val χ P)⁻¹ := by sorry
