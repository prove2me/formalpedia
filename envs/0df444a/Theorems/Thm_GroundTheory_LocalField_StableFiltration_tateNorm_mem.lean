-- Prove2me | Theorems.Thm_GroundTheory_LocalField_StableFiltration_tateNorm_mem
-- name    : GroundTheory.LocalField.StableFiltration.tateNorm_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:44:08.496637+00:00
-- url     : https://prove2.me/theorems/77204afb-e4e8-4083-9faa-619c09090290
-- title:
--   Stable Filtration: tate Norm mem
-- statement:
--   The Stable Filtration construction uses the tate Norm mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L173-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L173-L174

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

theorem GroundTheory.LocalField.StableFiltration.tateNorm_mem {n : ℕ} {x : V} (hx : x ∈ S.F n) : tateNorm G V x ∈ S.F n := by sorry
