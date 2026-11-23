-- Prove2me | Theorems.Thm_GroundTheory_LocalField_StableFiltration_subsingleton_tateZero_gr_iff
-- name    : GroundTheory.LocalField.StableFiltration.subsingleton_tateZero_gr_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:11.078225+00:00
-- url     : https://prove2.me/theorems/a59a7139-a53b-4150-ac21-9d8f9e7f2427
-- title:
--   Stable Filtration: subsingleton tate Zero gr iff
-- statement:
--   The Stable Filtration construction uses the subsingleton tate Zero gr iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L179-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L179-L200

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

theorem GroundTheory.LocalField.StableFiltration.subsingleton_tateZero_gr_iff (n : ℕ) :
    Subsingleton (TateZero G (S.gr n)) ↔
      ∀ x ∈ S.F n, (∀ g : G, g • x / x ∈ S.F (n + 1)) →
        ∃ y ∈ S.F n, x / tateNorm G V y ∈ S.F (n + 1) := by sorry
