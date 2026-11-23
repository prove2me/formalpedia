-- Prove2me | Theorems.Thm_GroundTheory_LocalField_StableFiltration_grMk_eq_grMk_iff
-- name    : GroundTheory.LocalField.StableFiltration.grMk_eq_grMk_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:03.87883+00:00
-- url     : https://prove2.me/theorems/6320dc06-f906-4ab2-9ce5-d55d5525b3bd
-- title:
--   Stable Filtration: gr Mk eq gr Mk iff
-- statement:
--   The Stable Filtration construction uses the gr Mk eq gr Mk iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L125-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L125-L128

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

theorem GroundTheory.LocalField.StableFiltration.grMk_eq_grMk_iff {n : ℕ} (x y : S.F n) :
    S.grMk n x = S.grMk n y ↔ (x : V) / y ∈ S.F (n + 1) := by sorry
