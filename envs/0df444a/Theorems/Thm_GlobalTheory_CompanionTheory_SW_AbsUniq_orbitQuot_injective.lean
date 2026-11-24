-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsUniq_orbitQuot_injective
-- name    : GlobalTheory.CompanionTheory.SW.AbsUniq.orbitQuot_injective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:01:27.307726+00:00
-- url     : https://prove2.me/theorems/01648aea-6f01-44a9-b38d-4696cb2b1d34
-- title:
--   Abs Uniq: orbit Quot injective
-- statement:
--   The Abs Uniq construction uses the orbit Quot injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ProperActionOrbitMeasure.lean#L39-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ProperActionOrbitMeasure.lean#L39-L49

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

theorem GlobalTheory.CompanionTheory.SW.AbsUniq.orbitQuot_injective {G V : Type} [Group G] (act : G → V → V) (h1 : ∀ x, act 1 x = x)
    (hm : ∀ g h x, act (g * h) x = act g (act h x)) (x₀ : V) :
    Function.Injective (orbitQuot act h1 hm x₀) := by sorry
