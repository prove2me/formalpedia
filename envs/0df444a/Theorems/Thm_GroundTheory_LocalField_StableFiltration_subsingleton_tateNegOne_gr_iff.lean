-- Prove2me | Theorems.Thm_GroundTheory_LocalField_StableFiltration_subsingleton_tateNegOne_gr_iff
-- name    : GroundTheory.LocalField.StableFiltration.subsingleton_tateNegOne_gr_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:35.537926+00:00
-- url     : https://prove2.me/theorems/22b0005b-5ed6-4904-88da-4f7bdcd84022
-- title:
--   Stable Filtration: subsingleton tate Neg One gr iff
-- statement:
--   The Stable Filtration construction uses the subsingleton tate Neg One gr iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L202-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L202-L223

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

theorem GroundTheory.LocalField.StableFiltration.subsingleton_tateNegOne_gr_iff (n : ℕ) :
    Subsingleton (TateNegOne G (S.gr n)) ↔
      ∀ x ∈ S.F n, tateNorm G V x ∈ S.F (n + 1) →
        ∃ m : G → V, (∀ g, m g ∈ S.F n) ∧ x / augMap G V m ∈ S.F (n + 1) := by sorry
