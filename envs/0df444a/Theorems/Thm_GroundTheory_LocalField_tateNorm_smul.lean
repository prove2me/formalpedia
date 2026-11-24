-- Prove2me | Theorems.Thm_GroundTheory_LocalField_tateNorm_smul
-- name    : GroundTheory.LocalField.tateNorm_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:44:54.267127+00:00
-- url     : https://prove2.me/theorems/5fa35e3c-d8a2-419f-a261-0d40b9300823
-- title:
--   Local Field: tate Norm smul
-- statement:
--   The Local Field construction uses the tate Norm smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L52-L54

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
variable (G M : Type*) [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
variable {G M}

theorem GroundTheory.LocalField.tateNorm_smul (g : G) (x : M) : tateNorm G M (g • x) = tateNorm G M x := by sorry
