-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_natCard_ker_eq
-- name    : GroundTheory.GroupCoh.natCard_ker_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:42:58.75082+00:00
-- url     : https://prove2.me/theorems/ad5710f6-7f32-47bc-b129-7d363136896a
-- title:
--   Group Coh: nat Card ker eq
-- statement:
--   The Group Coh construction uses the nat Card ker eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L59-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L59-L65

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

theorem GroundTheory.GroupCoh.natCard_ker_eq {f g : A →+ A} (hfg : ∀ x, f (g x) = 0) :
    Nat.card f.ker = Nat.card (KerModRange f g) * Nat.card g.range := by sorry
