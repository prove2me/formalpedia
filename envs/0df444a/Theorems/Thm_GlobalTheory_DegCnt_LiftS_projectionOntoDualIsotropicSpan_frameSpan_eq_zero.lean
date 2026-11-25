-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_LiftS_projectionOntoDualIsotropicSpan_frameSpan_eq_zero
-- name    : GlobalTheory.DegCnt.LiftS.projectionOntoDualIsotropicSpan_frameSpan_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:29:16.581174+00:00
-- url     : https://prove2.me/theorems/f28a2893-f13f-5748-92c7-e7a85dda16ce
-- title:
--   Lift S: projection Onto Dual Isotropic Span frame Span eq zero
-- statement:
--   The Lift S construction uses the projection Onto Dual Isotropic Span frame Span eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormCongruenceLiftSmallGroup.lean#L427-L429
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormCongruenceLiftSmallGroup.lean#L427-L429

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormCongruenceLiftSmallGroup
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.LiftS
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)

theorem GlobalTheory.DegCnt.LiftS.projectionOntoDualIsotropicSpan_frameSpan_eq_zero {y : V} (hy : y ∈ V0 N.F N.F') : qI N y = 0 := by sorry
