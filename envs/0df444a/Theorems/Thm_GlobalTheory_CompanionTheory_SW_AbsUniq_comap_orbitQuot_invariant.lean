-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsUniq_comap_orbitQuot_invariant
-- name    : GlobalTheory.CompanionTheory.SW.AbsUniq.comap_orbitQuot_invariant
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:00:52.804216+00:00
-- url     : https://prove2.me/theorems/fbf46361-d992-4b2f-a711-d4ebab997eef
-- title:
--   Abs Uniq: comap orbit Quot invariant
-- statement:
--   The Abs Uniq construction uses the comap orbit Quot invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ProperActionOrbitMeasure.lean#L131-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ProperActionOrbitMeasure.lean#L131-L159

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

theorem GlobalTheory.CompanionTheory.SW.AbsUniq.comap_orbitQuot_invariant {G V : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace V] [T2Space V] [SecondCountableTopology V] [MeasurableSpace V]
    [BorelSpace V] (act : G → V → V) (hc : Continuous fun p : G × V => act p.1 p.2)
    (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V)
    (hφ : MeasurableEmbedding (orbitQuot act h1 hm x₀)) (μ : Measure V)
    (hμ : ∀ g, μ.map (act g) = μ) (g : G) (s : Set (G ⧸ stabilizerOf act h1 hm x₀))
    (hs : MeasurableSet s) :
    μ.comap (orbitQuot act h1 hm x₀) ((fun y => g • y) ⁻¹' s) =
      μ.comap (orbitQuot act h1 hm x₀) s := by sorry
