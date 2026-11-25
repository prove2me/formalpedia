-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SplitUnramifiedPlaces_nonempty_splitPlace_five
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.nonempty_splitPlace_five
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:09:51.106257+00:00
-- url     : https://prove2.me/theorems/b64d7095-7f04-4fa8-9056-505b8a4c4d00
-- title:
--   Split Unramified Places: nonempty split Place five
-- statement:
--   The Split Unramified Places construction uses the nonempty split Place five property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SplitUnramifiedPlaces.lean#L249-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SplitUnramifiedPlaces.lean#L249-L251

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.nonempty_splitPlace_five : Nonempty (SplitPlace 5 GaussianInt) := by sorry
