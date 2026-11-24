-- Prove2me | Theorems.Thm_GroundTheory_LocalField_StableFiltration_augMap_mem
-- name    : GroundTheory.LocalField.StableFiltration.augMap_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:44:14.82984+00:00
-- url     : https://prove2.me/theorems/03c4c043-e1c0-42d5-97a8-8d35bdcc80f6
-- title:
--   Stable Filtration: aug Map mem
-- statement:
--   The Stable Filtration construction uses the aug Map mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L176-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L176-L177

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

theorem GroundTheory.LocalField.StableFiltration.augMap_mem {n : ℕ} {m : G → V} (hm : ∀ g, m g ∈ S.F n) : augMap G V m ∈ S.F n := by sorry
