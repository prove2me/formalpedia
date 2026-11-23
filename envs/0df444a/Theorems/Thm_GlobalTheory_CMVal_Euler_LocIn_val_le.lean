-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_LocIn_val_le
-- name    : GlobalTheory.CMVal.Euler.LocIn.val_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:02:13.876242+00:00
-- url     : https://prove2.me/theorems/73c84362-2921-4c07-a592-4ae6a2f7344b
-- title:
--   Loc In: val le
-- statement:
--   The Loc In construction uses the val le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValIotaLeOfMem.lean#L78-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValIotaLeOfMem.lean#L78-L83

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

theorem GlobalTheory.CMVal.Euler.LocIn.val_le {n : ℕ} {v : HeightOneSpectrum (OF E)} {z : Af E} (h : LocIn n v z) {P : HeightOneSpectrum (𝓞 E)}
    (hP : Over P v) : Valued.v (z P) ≤ 1 := by sorry
