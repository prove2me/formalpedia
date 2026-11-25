-- Prove2me | Theorems.Thm_GroundTheory_LocalField_filtrationComplete_of_hasBasis
-- name    : GroundTheory.LocalField.filtrationComplete_of_hasBasis
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:44:22.075277+00:00
-- url     : https://prove2.me/theorems/ce41f865-4f83-4fd7-8ab1-59cabdf58039
-- title:
--   Local Field: filtration Complete of has Basis
-- statement:
--   The Local Field construction uses the filtration Complete of has Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FilteredSurj.lean#L153-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FilteredSurj.lean#L153-L171

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

theorem GroundTheory.LocalField.filtrationComplete_of_hasBasis {G : Type*} [Group G] [UniformSpace G]
    [IsRightUniformGroup G] [CompleteSpace G] {F : ℕ → Subgroup G}
    (hb : (𝓝 (1 : G)).HasBasis (fun _ => True) (fun n => (F n : Set G))) :
    FiltrationComplete F := by sorry
