-- Prove2me | Theorems.Thm_GlobalTheory_StepData_NormalForm_exists_valuation_eq_zpow
-- name    : GlobalTheory.StepData.NormalForm.exists_valuation_eq_zpow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:54:33.556618+00:00
-- url     : https://prove2.me/theorems/6fd30bc3-d3ba-5bd9-a38a-a8019f87d225
-- title:
--   Normal Form: exists valuation eq zpow
-- statement:
--   The Normal Form construction uses the exists valuation eq zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsValuationEqZpow.lean#L21-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsValuationEqZpow.lean#L21-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsValuationEqZpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.StepData GlobalTheory.StepData.NormalForm
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open MeasureTheory ValuativeRel Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.StepData.NormalForm.exists_valuation_eq_zpow {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k)
    (d : kˣ) : ∃ e : ℤ, valuation k (d : k) = valuation k (ϖ : k) ^ e := by sorry
