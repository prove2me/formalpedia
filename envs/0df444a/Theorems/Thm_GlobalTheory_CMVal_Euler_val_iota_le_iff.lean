-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_val_iota_le_iff
-- name    : GlobalTheory.CMVal.Euler.val_iota_le_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:02:11.117815+00:00
-- url     : https://prove2.me/theorems/136b5dbb-d055-4da6-ba85-f3bf4001529d
-- title:
--   Euler: val iota le iff
-- statement:
--   The Euler construction uses the val iota le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValIotaLeOfMem.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValIotaLeOfMem.lean#L43-L48

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

theorem GlobalTheory.CMVal.Euler.val_iota_le_iff (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (a : OF E) :
    Valued.v (iota a P) ≤ WithZero.exp (-(n : ℤ)) ↔ algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal ^ n := by sorry
