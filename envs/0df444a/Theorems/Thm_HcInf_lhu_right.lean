-- Prove2me | Theorems.Thm_HcInf_lhu_right
-- name    : HcInf.lhu_right
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:11:14.883896+00:00
-- url     : https://prove2.me/theorems/e9d142ac-f944-5933-b305-a5e7e51deac4
-- title:
--   Hc Inf: lhu right
-- statement:
--   The Hc Inf construction uses the lhu right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExLHU.lean#L15-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExLHU.lean#L15-L30

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExLHU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HcInf
open MeasureTheory Filter Topology
open scoped ENNReal NNReal Pointwise
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem HcInf.lhu_right (m : Measure G) [m.IsHaarMeasure] (z : G) :
    ∃ r : ℝ≥0∞, ∀ B : Set G, MeasurableSet B → m {x | x * z ∈ B} = r * m B := by sorry
