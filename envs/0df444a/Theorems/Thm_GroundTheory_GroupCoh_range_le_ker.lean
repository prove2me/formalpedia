-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_range_le_ker
-- name    : GroundTheory.GroupCoh.range_le_ker
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:43:14.932805+00:00
-- url     : https://prove2.me/theorems/58c4c0a9-1cc4-4943-bdd1-4231457d692a
-- title:
--   Group Coh: range le ker
-- statement:
--   The Group Coh construction uses the range le ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L45-L48

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.GroupCoh
variable {A : Type*} [AddCommGroup A]

theorem GroundTheory.GroupCoh.range_le_ker {f g : A →+ A} (hfg : ∀ x, f (g x) = 0) : g.range ≤ f.ker := by sorry
