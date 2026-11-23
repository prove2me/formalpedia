-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_val_iota_le_of_mem
-- name    : GlobalTheory.CMVal.Euler.val_iota_le_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:01:52.345397+00:00
-- url     : https://prove2.me/theorems/20d75214-8b28-42f9-9f3f-c5048932bd79
-- title:
--   Euler: val iota le of mem
-- statement:
--   The Euler construction uses the val iota le of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValIotaLeOfMem.lean#L53-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValIotaLeOfMem.lean#L53-L61

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

theorem GlobalTheory.CMVal.Euler.val_iota_le_of_mem {P : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (OF E)} (h : Over P v) (n : ℕ) {a : OF E}
    (ha : a ∈ v.asIdeal ^ n) : Valued.v (iota a P) ≤ WithZero.exp (-(n : ℤ)) := by sorry
