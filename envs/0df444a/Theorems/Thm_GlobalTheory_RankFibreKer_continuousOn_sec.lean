-- Prove2me | Theorems.Thm_GlobalTheory_RankFibreKer_continuousOn_sec
-- name    : GlobalTheory.RankFibreKer.continuousOn_sec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:15:11.55955+00:00
-- url     : https://prove2.me/theorems/db433975-6b4e-4643-a50b-affd9a90d8c7
-- title:
--   Rank Fibre Ker: continuous On sec
-- statement:
--   The Rank Fibre Ker construction uses the continuous On sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FibreZeroMemCoinvariants.lean#L39-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FibreZeroMemCoinvariants.lean#L39-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoinvariantOfLocallyConstantTwistStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrbitalIntegralVanishesOfFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankIffNonzeroMinorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFirstMaximalMinorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionInverseIntoSliceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FirstMaximalMinorLocallyConstantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SliceStabilizerTrivialStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousSliceSectionMeasureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousSliceSectionIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SliceSectionHaarDecompositionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompactCoveredByOpenCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarIntegralOverCosetRepresentativesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreZeroMemCoinvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil
open GlobalTheory GlobalTheory.RankFibreKer
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.RankFibreKer.continuousOn_sec {a d : ℕ} : ContinuousOn (sec (k := k) (a := a) (d := d)) {Y | Y.rank = a} := by sorry
