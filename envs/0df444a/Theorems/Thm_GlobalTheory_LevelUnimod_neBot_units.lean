-- Prove2me | Theorems.Thm_GlobalTheory_LevelUnimod_neBot_units
-- name    : GlobalTheory.LevelUnimod.neBot_units
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:03:16.396849+00:00
-- url     : https://prove2.me/theorems/6eec9e48-32d3-4e50-b5a1-6474e55c0341
-- title:
--   Level Unimod: ne Bot units
-- statement:
--   The Level Unimod construction uses the ne Bot units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsUnimodularBlockUpperTriangularSymmetricLevels.lean#L156-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsUnimodularBlockUpperTriangularSymmetricLevels.lean#L156-L160

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GlCharacterEqOneOfTransposeInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsUnimodularBlockUpperTriangularSymmetricLevels
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped Topology
open GlobalTheory GlobalTheory.LevelUnimod
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.LevelUnimod.neBot_units : (Filter.comap (Units.val : kˣ → k) (𝓝 0)).NeBot := by sorry
