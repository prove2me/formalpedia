-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_OrderUnits_val_int_le
-- name    : GlobalTheory.CMVal.OrderUnits.val_int_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:57:50.284488+00:00
-- url     : https://prove2.me/theorems/6dcd1fb1-f879-4cd7-bb93-2027cfac6a1f
-- title:
--   Order Units: val int le
-- statement:
--   The Order Units construction uses the val int le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinPartEqOneOfLevel.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinPartEqOneOfLevel.lean#L32-L36

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.OrderUnits
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.OrderUnits.val_int_le (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (b : 𝓞 E) (hb : b ∈ P.asIdeal ^ n) :
    Valued.v (algebraMap E (Af E) (algebraMap (𝓞 E) E b) P) ≤ WithZero.exp (-(n : ℤ)) := by sorry
