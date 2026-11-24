-- Prove2me | Theorems.Thm_GlobalTheory_RankFibreKer_fibre_ker
-- name    : GlobalTheory.RankFibreKer.fibre_ker
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:14:15.00407+00:00
-- url     : https://prove2.me/theorems/08e98f6e-26d1-4c01-afd6-0467405b8c7b
-- title:
--   Rank Fibre Ker: fibre ker
-- statement:
--   The Rank Fibre Ker construction uses the fibre ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FibreZeroMemCoinvariants.lean#L65-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FibreZeroMemCoinvariants.lean#L65-L147

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

theorem GlobalTheory.RankFibreKer.fibre_ker : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν →
    GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b),
    GlobalTheory.RankFibre.fibre ν β a b Φ = 0 → Φ ∈ GlobalTheory.RankFibre.coinv ν β a (a + b) := by sorry
