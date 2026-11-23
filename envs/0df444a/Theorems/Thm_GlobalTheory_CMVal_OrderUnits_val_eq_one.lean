-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_OrderUnits_val_eq_one
-- name    : GlobalTheory.CMVal.OrderUnits.val_eq_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:02.594802+00:00
-- url     : https://prove2.me/theorems/56a26302-b380-4681-a3f2-5a2b3c51b56a
-- title:
--   Order Units: val eq one
-- statement:
--   The Order Units construction uses the val eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinPartEqOneOfLevel.lean#L80-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinPartEqOneOfLevel.lean#L80-L90

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

theorem GlobalTheory.CMVal.OrderUnits.val_eq_one {c : Ideal (OF E)} {y : (Af E)ˣ} (hy : y ∈ hatOUnits c) (P : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((y : Af E) P) = 1 := by sorry
