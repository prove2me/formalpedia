-- Prove2me | Theorems.Thm_GlobalTheory_Tw_apply_out_mk
-- name    : GlobalTheory.Tw.apply_out_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:16.285049+00:00
-- url     : https://prove2.me/theorems/9c536575-ebfd-4b3a-afa7-49f756bbf387
-- title:
--   Tw: apply out mk
-- statement:
--   The Tw construction uses the apply out mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/QuotIntegrableIffCutoff.lean#L35-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/QuotIntegrableIffCutoff.lean#L35-L41

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
omit [MeasurableSpace G]

theorem GlobalTheory.Tw.apply_out_mk {T : Subgroup G} {α : Type} {F : G → α} (hF : ∀ t ∈ T, ∀ x, F (t * x) = F x) (x : G) :
    F (Quotient.out (Quotient.mk (QuotientGroup.rightRel T) x)) = F x := by sorry
