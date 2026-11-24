-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_mul_mem_of_isClosed
-- name    : GroundTheory.Global.Cyclotomic.mul_mem_of_isClosed
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:38:14.619055+00:00
-- url     : https://prove2.me/theorems/bdbda631-0845-42fb-81b3-c7c964d75550
-- title:
--   Cyclotomic: mul mem of is Closed
-- statement:
--   The Cyclotomic construction uses the mul mem of is Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/ClosedSubgroups.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/ClosedSubgroups.lean#L17-L23

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

theorem GroundTheory.Global.Cyclotomic.mul_mem_of_isClosed (H : AddSubgroup ℤ_[ℓ]) (hH : IsClosed (H : Set ℤ_[ℓ])) {x : ℤ_[ℓ]}
    (hx : x ∈ H) (t : ℤ_[ℓ]) : x * t ∈ H := by sorry
