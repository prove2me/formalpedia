-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Fibre_continuous_finPart
-- name    : GlobalTheory.CMVal.Fibre.continuous_finPart
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:04:19.020835+00:00
-- url     : https://prove2.me/theorems/ddac9bdb-54b9-47d0-a3c3-6370dccf8c2d
-- title:
--   Fibre: continuous fin Part
-- statement:
--   The Fibre construction uses the continuous fin Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinPartEqOneOfFibres.lean#L71-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinPartEqOneOfFibres.lean#L71-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Fibre
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.Fibre.continuous_finPart (χ : HChar E) : Continuous (finPart χ) := by sorry
