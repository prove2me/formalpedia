-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_UpLatIndex_mem_ordBall
-- name    : GlobalTheory.BorelUMod.UpLatIndex.mem_ordBall
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:45.362714+00:00
-- url     : https://prove2.me/theorems/6d102c01-e9f4-4152-b68f-ee9ef8d1d018
-- title:
--   Up Lat Index: mem ord Ball
-- statement:
--   The Up Lat Index construction uses the mem ord Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexUpLatEqProd.lean#L21-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexUpLatEqProd.lean#L21-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod GlobalTheory.BorelUMod.UpLatIndex
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.BorelUMod.UpLatIndex.mem_ordBall {k : ℤ} {x : L} : x ∈ ordBall L k ↔ Valued.v x ≤ WithZero.exp (-k) := by sorry
