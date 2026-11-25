-- Prove2me | Theorems.Thm_GroundTheory_LocalField_subsingleton_tateNegOne_of_complete
-- name    : GroundTheory.LocalField.subsingleton_tateNegOne_of_complete
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:45:01.117363+00:00
-- url     : https://prove2.me/theorems/c3534984-23d8-4f88-8c04-31f6b9dcd0ef
-- title:
--   Local Field: subsingleton tate Neg One of complete
-- statement:
--   The Local Field construction uses the subsingleton tate Neg One of complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L274-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L274-L303

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Finset Filter
variable {V : Type*} [CommGroup V]
variable {G : Type*} [Group G] [Fintype G] [MulDistribMulAction G V]

theorem GroundTheory.LocalField.subsingleton_tateNegOne_of_complete (S : StableFiltration G V) (h0 : S.F 0 = ⊤)
    (hc : FiltrationComplete S.F) (hs : FiltrationSeparated S.F)
    (hgr : ∀ n, Subsingleton (TateNegOne G (S.gr n))) : Subsingleton (TateNegOne G V) := by sorry
