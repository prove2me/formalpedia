-- Prove2me | Theorems.Thm_GroundTheory_LocalField_StableFiltration_tateNorm_grMk
-- name    : GroundTheory.LocalField.StableFiltration.tateNorm_grMk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:11.020252+00:00
-- url     : https://prove2.me/theorems/53a20487-cc9a-4408-b002-521306628368
-- title:
--   Stable Filtration: tate Norm gr Mk
-- statement:
--   The Stable Filtration construction uses the tate Norm gr Mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L163-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L163-L166

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

theorem GroundTheory.LocalField.StableFiltration.tateNorm_grMk {n : ℕ} (x : S.F n) :
    tateNorm G (S.gr n) (S.grMk n x) = S.grMk n (tateNorm G (S.F n) x) := by sorry
