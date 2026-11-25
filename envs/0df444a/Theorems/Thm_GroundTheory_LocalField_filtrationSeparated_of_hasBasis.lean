-- Prove2me | Theorems.Thm_GroundTheory_LocalField_filtrationSeparated_of_hasBasis
-- name    : GroundTheory.LocalField.filtrationSeparated_of_hasBasis
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:45:11.177848+00:00
-- url     : https://prove2.me/theorems/f1d114a7-9a0b-4d41-b49d-c3176b1b5554
-- title:
--   Local Field: filtration Separated of has Basis
-- statement:
--   The Local Field construction uses the filtration Separated of has Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FilteredSurj.lean#L175-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FilteredSurj.lean#L175-L183

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
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
open Filter Topology Uniformity

theorem GroundTheory.LocalField.filtrationSeparated_of_hasBasis {H : Type*} [Group H] [TopologicalSpace H] [T1Space H]
    {E : ℕ → Subgroup H}
    (hb : (𝓝 (1 : H)).HasBasis (fun _ => True) (fun n => (E n : Set H))) :
    FiltrationSeparated E := by sorry
