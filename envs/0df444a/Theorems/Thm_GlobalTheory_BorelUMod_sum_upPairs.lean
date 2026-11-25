-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_sum_upPairs
-- name    : GlobalTheory.BorelUMod.sum_upPairs
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:00:12.140963+00:00
-- url     : https://prove2.me/theorems/8222655c-3514-4bc2-a0be-c16063c79a43
-- title:
--   Borel UMod: sum up Pairs
-- statement:
--   The Borel UMod construction uses the sum up Pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealWeight.lean#L95-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealWeight.lean#L95-L111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexEqOfSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnipLatIsOpenIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Formalism.UG
open scoped NNReal
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem GlobalTheory.BorelUMod.sum_upPairs (a : Fin n → ℤ) :
    ∑ p ∈ upPairs n, (a p.1 - a p.2) = ∑ i, a i * ((n : ℤ) - 1 - 2 * i.val) := by sorry
