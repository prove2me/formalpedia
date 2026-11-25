-- Prove2me | Theorems.Thm_HcInf_lhu_key
-- name    : HcInf.lhu_key
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:13:46.150628+00:00
-- url     : https://prove2.me/theorems/9907b41f-ab8f-480b-995b-45396a3dc586
-- title:
--   Hc Inf: lhu key
-- statement:
--   The Hc Inf construction uses the lhu key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExLHU.lean#L32-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExLHU.lean#L32-L95

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

theorem HcInf.lhu_key (m : Measure G) [m.IsHaarMeasure] (β : Measure G) (W V : Set G)
    (hinv : ∀ (h : G) (S : Set G), MeasurableSet S → S ⊆ W → (fun g => h * g) '' S ⊆ W →
      β ((fun g => h * g) '' S) = β S)
    (hVc : IsCompact V) (hVW : V ⊆ W) (hVW' : ∀ v ∈ V, v⁻¹ ∈ W) (hβV : β V ≠ ⊤) (hβVi : β V⁻¹ ≠ ⊤) :
    ∃ K : ℝ≥0∞, ∀ B : Set G, MeasurableSet B → B ⊆ V → m V * β B = K * m B := by sorry
