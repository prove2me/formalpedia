-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_locIn_congr
-- name    : GlobalTheory.CMVal.Euler.locIn_congr
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:04:14.267327+00:00
-- url     : https://prove2.me/theorems/8fa6e146-a699-4b83-aa71-524c4d501d80
-- title:
--   Euler: loc In congr
-- statement:
--   The Euler construction uses the loc In congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValIotaLeOfMem.lean#L88-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValIotaLeOfMem.lean#L88-L90

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

theorem GlobalTheory.CMVal.Euler.locIn_congr {n : ℕ} {v : HeightOneSpectrum (OF E)} {z z' : Af E} (h : ∀ P, Over P v → z P = z' P) :
    LocIn n v z ↔ LocIn n v z' := by sorry
