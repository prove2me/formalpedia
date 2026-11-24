-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsUniq_measurableEmbedding_orbitQuot
-- name    : GlobalTheory.CompanionTheory.SW.AbsUniq.measurableEmbedding_orbitQuot
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:01:26.249158+00:00
-- url     : https://prove2.me/theorems/748bdb0f-6cd1-4311-9d93-7c3636a8754f
-- title:
--   Abs Uniq: measurable Embedding orbit Quot
-- statement:
--   The Abs Uniq construction uses the measurable Embedding orbit Quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ProperActionOrbitMeasure.lean#L79-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ProperActionOrbitMeasure.lean#L79-L129

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QuotMeasUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ProperActionOrbitMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.AbsUniq

theorem GlobalTheory.CompanionTheory.SW.AbsUniq.measurableEmbedding_orbitQuot {G V : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace V] [T2Space V] [SecondCountableTopology V] [MeasurableSpace V]
    [BorelSpace V] (act : G → V → V) (hc : Continuous fun p : G × V => act p.1 p.2)
    (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) (Z : Set V) (hZ : IsClosed Z)
    (hx : x₀ ∈ Z) (hinv : ∀ g, ∀ x ∈ Z, act g x ∈ Z)
    (htr : ∀ x ∈ Z, ∀ y ∈ Z, ∃ g, act g x = y) :
    MeasurableEmbedding (orbitQuot act h1 hm x₀) := by sorry
