-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_UpLatIndex_ordBall_mono
-- name    : GlobalTheory.BorelUMod.UpLatIndex.ordBall_mono
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:01:35.469547+00:00
-- url     : https://prove2.me/theorems/bba5d293-6444-4c32-a2db-b6407f1e01ec
-- title:
--   Up Lat Index: ord Ball mono
-- statement:
--   The Up Lat Index construction uses the ord Ball mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexUpLatEqProd.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexUpLatEqProd.lean#L23-L24

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

theorem GlobalTheory.BorelUMod.UpLatIndex.ordBall_mono {k K : ℤ} (h : k ≤ K) : ordBall L K ≤ ordBall L k := by sorry
