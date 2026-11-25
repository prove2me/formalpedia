-- Prove2me | Theorems.Thm_GlobalTheory_Mass_PrimCount_one_le_rd
-- name    : GlobalTheory.Mass.PrimCount.one_le_rd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:40:13.167089+00:00
-- url     : https://prove2.me/theorems/26edce30-58cc-5cce-aa39-1f2b6ab5fa62
-- title:
--   Prim Count: one le rd
-- statement:
--   The Prim Count construction uses the one le rd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatInIsLattice.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatInIsLattice.lean#L42-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsShortVectorIntegralHermitianLatticeRankOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardShortVectorsLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsRest
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatInIsLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.PrimCount

theorem GlobalTheory.Mass.PrimCount.one_le_rd (K : Type) [Field K] [NumberField K] : 1 ≤ 2 * vInv K := by sorry
