-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_LocIn_inv
-- name    : GlobalTheory.CMVal.Euler.LocIn.inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:34.71388+00:00
-- url     : https://prove2.me/theorems/e3249335-0ac0-430e-ae6c-f6f85361ad90
-- title:
--   Loc In: inv
-- statement:
--   The Loc In construction uses the inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValIotaLeOfMem.lean#L109-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValIotaLeOfMem.lean#L109-L137

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

theorem GlobalTheory.CMVal.Euler.LocIn.inv {n : ℕ} {v : HeightOneSpectrum (OF E)} {y : (Af E)ˣ} (h : LocIn n v y)
    (hu : ∀ P, Over P v → Valued.v ((y : Af E) P) = 1) : LocIn n v (y⁻¹ : (Af E)ˣ) := by sorry
