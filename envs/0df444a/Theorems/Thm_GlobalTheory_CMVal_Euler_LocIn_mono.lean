-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_LocIn_mono
-- name    : GlobalTheory.CMVal.Euler.LocIn.mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:05.135612+00:00
-- url     : https://prove2.me/theorems/8d2da36b-75b9-4adc-8a37-7b2f5ab4b9ce
-- title:
--   Loc In: mono
-- statement:
--   The Loc In construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValIotaLeOfMem.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValIotaLeOfMem.lean#L74-L76

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.Euler.LocIn.mono {m n : ℕ} {v : HeightOneSpectrum (OF E)} {z : Af E} (h : LocIn n v z) (hm : m ≤ n) : LocIn m v z := by sorry
