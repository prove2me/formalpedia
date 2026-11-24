-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_locIn_of_sub_one
-- name    : GlobalTheory.CMVal.Euler.locIn_of_sub_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:05:21.369992+00:00
-- url     : https://prove2.me/theorems/6b36c0f8-cd11-4bb3-91e0-74b3a5f8fe57
-- title:
--   Euler: loc In of sub one
-- statement:
--   The Euler construction uses the loc In of sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValIotaLeOfMem.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValIotaLeOfMem.lean#L92-L94

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

theorem GlobalTheory.CMVal.Euler.locIn_of_sub_one {n : ℕ} {v : HeightOneSpectrum (OF E)} {z : Af E}
    (h : ∀ P, Over P v → Valued.v (z P - 1) ≤ WithZero.exp (-(n : ℤ))) : LocIn n v z := by sorry
