-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsUniq_invariant_measure_unique
-- name    : GlobalTheory.CompanionTheory.SW.AbsUniq.invariant_measure_unique
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:00:54.555469+00:00
-- url     : https://prove2.me/theorems/c474693c-66a9-49c4-9736-7827437ea964
-- title:
--   Abs Uniq: invariant measure unique
-- statement:
--   The Abs Uniq construction uses the invariant measure unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ProperActionOrbitMeasure.lean#L161-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ProperActionOrbitMeasure.lean#L161-L228

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

theorem GlobalTheory.CompanionTheory.SW.AbsUniq.invariant_measure_unique :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
      (V : Type) [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
      [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (act : G → V → V),
      (Continuous fun p : G × V => act p.1 p.2) → (∀ x, act 1 x = x) →
      (∀ g h x, act (g * h) x = act g (act h x)) → ∀ Z : Set V, IsClosed Z →
      (∀ g, ∀ x ∈ Z, act g x ∈ Z) → (∀ x ∈ Z, ∀ y ∈ Z, ∃ g, act g x = y) →
      ∀ (μ ν : Measure V), IsLocallyFiniteMeasure μ → IsLocallyFiniteMeasure ν → μ Zᶜ = 0 →
      ν Zᶜ = 0 → (∀ g, μ.map (act g) = μ) → (∀ g, ν.map (act g) = ν) → ν ≠ 0 →
      ∃ c : ℝ≥0, μ = c • ν := by sorry
