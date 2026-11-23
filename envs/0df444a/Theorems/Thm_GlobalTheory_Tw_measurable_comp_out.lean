-- Prove2me | Theorems.Thm_GlobalTheory_Tw_measurable_comp_out
-- name    : GlobalTheory.Tw.measurable_comp_out
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:07.363687+00:00
-- url     : https://prove2.me/theorems/bfcd2617-dd75-4af8-874c-1e801d91efa9
-- title:
--   Tw: measurable comp out
-- statement:
--   The Tw construction uses the measurable comp out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/QuotIntegrableIffCutoff.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/QuotIntegrableIffCutoff.lean#L43-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_BruhatFunctionExistsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_QuotIntegrableIffCutoff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.Tw
variable {G : Type} [Group G] [MeasurableSpace G]

theorem GlobalTheory.Tw.measurable_comp_out {T : Subgroup G} {α : Type} [MeasurableSpace α] {F : G → α} (hm : Measurable F)
    (hF : ∀ t ∈ T, ∀ x, F (t * x) = F x) : Measurable fun c : RCoset T => F (Quotient.out c) := by sorry
