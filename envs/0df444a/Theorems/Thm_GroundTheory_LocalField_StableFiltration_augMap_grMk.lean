-- Prove2me | Theorems.Thm_GroundTheory_LocalField_StableFiltration_augMap_grMk
-- name    : GroundTheory.LocalField.StableFiltration.augMap_grMk
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:43:47.321203+00:00
-- url     : https://prove2.me/theorems/66d784d8-86ed-4216-a42a-32a13eb490b3
-- title:
--   Stable Filtration: aug Map gr Mk
-- statement:
--   The Stable Filtration construction uses the aug Map gr Mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L168-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L168-L171

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
open GroundTheory.LocalField.StableFiltration
variable {G V : Type*} [Group G] [CommGroup V] [MulDistribMulAction G V]
  (S : StableFiltration G V)
variable [Fintype G]

theorem GroundTheory.LocalField.StableFiltration.augMap_grMk {n : ℕ} (m : G → S.F n) :
    augMap G (S.gr n) (fun g => S.grMk n (m g)) = S.grMk n (augMap G (S.F n) m) := by sorry
