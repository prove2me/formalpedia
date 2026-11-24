-- Prove2me | Theorems.Thm_GlobalTheory_LevelUnimod_smul_inj
-- name    : GlobalTheory.LevelUnimod.smul_inj
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:03:11.478504+00:00
-- url     : https://prove2.me/theorems/6ea017cb-6035-493f-baa9-5431a306140b
-- title:
--   Level Unimod: smul inj
-- statement:
--   The Level Unimod construction uses the smul inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsUnimodularBlockUpperTriangularSymmetricLevels.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsUnimodularBlockUpperTriangularSymmetricLevels.lean#L19-L23

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
open scoped Pointwise NNReal ENNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
omit [SecondCountableTopology G] [T2Space G] [BorelSpace G]

theorem GlobalTheory.LevelUnimod.smul_inj {μ : Measure G} [μ.IsHaarMeasure] {a b : ℝ≥0} (h : a • μ = b • μ) : a = b := by sorry
