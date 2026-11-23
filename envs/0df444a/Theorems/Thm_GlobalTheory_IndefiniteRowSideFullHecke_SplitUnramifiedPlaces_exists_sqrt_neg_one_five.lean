-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SplitUnramifiedPlaces_exists_sqrt_neg_one_five
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.exists_sqrt_neg_one_five
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:26.898821+00:00
-- url     : https://prove2.me/theorems/de16e1fd-9ba0-4bd6-a754-f76a7e5d343d
-- title:
--   Split Unramified Places: exists sqrt neg one five
-- statement:
--   The Split Unramified Places construction uses the exists sqrt neg one five property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SplitUnramifiedPlaces.lean#L228-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SplitUnramifiedPlaces.lean#L228-L247

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SplitUnramifiedPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
variable {p : ℕ} [Fact p.Prime]
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces._p2m_local_instance_3272e94269_226

theorem GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.exists_sqrt_neg_one_five : ∃ s h : ℤ_[5], s * s = -1 ∧ 2 * h = 1 := by sorry
