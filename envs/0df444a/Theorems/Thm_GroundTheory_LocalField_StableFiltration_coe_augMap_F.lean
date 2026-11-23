-- Prove2me | Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_augMap_F
-- name    : GroundTheory.LocalField.StableFiltration.coe_augMap_F
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:04.829266+00:00
-- url     : https://prove2.me/theorems/64aa9629-837d-4501-8817-a023d4e455ac
-- title:
--   Stable Filtration: coe aug Map F
-- statement:
--   The Stable Filtration construction uses the coe aug Map F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L158-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L158-L161

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

theorem GroundTheory.LocalField.StableFiltration.coe_augMap_F {n : ℕ} (m : G → S.F n) :
    ((augMap G (S.F n) m : S.F n) : V) = augMap G V (fun g => (m g : V)) := by sorry
