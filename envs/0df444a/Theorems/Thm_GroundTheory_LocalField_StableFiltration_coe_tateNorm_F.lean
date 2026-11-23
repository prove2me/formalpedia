-- Prove2me | Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_tateNorm_F
-- name    : GroundTheory.LocalField.StableFiltration.coe_tateNorm_F
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:52.902167+00:00
-- url     : https://prove2.me/theorems/5f53f6db-1d19-44ee-afc0-8dbed93e0f13
-- title:
--   Stable Filtration: coe tate Norm F
-- statement:
--   The Stable Filtration construction uses the coe tate Norm F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L154-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L154-L156

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

theorem GroundTheory.LocalField.StableFiltration.coe_tateNorm_F {n : ℕ} (x : S.F n) : ((tateNorm G (S.F n) x : S.F n) : V) = tateNorm G V x := by sorry
