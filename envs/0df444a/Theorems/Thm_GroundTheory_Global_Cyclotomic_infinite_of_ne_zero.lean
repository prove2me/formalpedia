-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_infinite_of_ne_zero
-- name    : GroundTheory.Global.Cyclotomic.infinite_of_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:59.94819+00:00
-- url     : https://prove2.me/theorems/7901961a-891c-4b22-b0c2-cbf34ed20aa2
-- title:
--   Cyclotomic: infinite of ne zero
-- statement:
--   The Cyclotomic construction uses the infinite of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/ClosedSubgroups.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/ClosedSubgroups.lean#L44-L50

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem GroundTheory.Global.Cyclotomic.infinite_of_ne_zero (H : AddSubgroup ℤ_[ℓ]) {x : ℤ_[ℓ]} (hx : x ∈ H) (hx0 : x ≠ 0) :
    (H : Set ℤ_[ℓ]).Infinite := by sorry
