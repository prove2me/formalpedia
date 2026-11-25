-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_NormOneCount_card_torsion_le
-- name    : GlobalTheory.DegCnt.NormOneCount.card_torsion_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:00:46.382659+00:00
-- url     : https://prove2.me/theorems/c04b1896-a460-410b-8e96-26f068bdc8fd
-- title:
--   Norm One Count: card torsion le
-- statement:
--   The Norm One Count construction uses the card torsion le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsIntegralOfMulMem.lean#L57-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsIntegralOfMulMem.lean#L57-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfMulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.NormOneCount

theorem GlobalTheory.DegCnt.NormOneCount.card_torsion_le (K : Type) [Field K] [NumberField K] :
    Nat.card (Units.torsion K) ≤ 2 * Module.finrank ℚ K ^ 2 := by sorry
