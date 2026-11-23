-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsUniq_range_orbitQuot
-- name    : GlobalTheory.CompanionTheory.SW.AbsUniq.range_orbitQuot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:23:48.020518+00:00
-- url     : https://prove2.me/theorems/8c414a84-68d8-49cf-a342-3596a071f5a7
-- title:
--   Abs Uniq: range orbit Quot
-- statement:
--   The Abs Uniq construction uses the range orbit Quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ProperActionOrbitMeasure.lean#L59-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ProperActionOrbitMeasure.lean#L59-L70

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

theorem GlobalTheory.CompanionTheory.SW.AbsUniq.range_orbitQuot {G V : Type} [Group G] (act : G → V → V) (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) (Z : Set V) (hx : x₀ ∈ Z)
    (hinv : ∀ g, ∀ x ∈ Z, act g x ∈ Z) (htr : ∀ x ∈ Z, ∀ y ∈ Z, ∃ g, act g x = y) :
    Set.range (orbitQuot act h1 hm x₀) = Z := by sorry
