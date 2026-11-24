-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_isOpen_of_isClosed_of_ne_zero
-- name    : GroundTheory.Global.Cyclotomic.isOpen_of_isClosed_of_ne_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:37:54.387976+00:00
-- url     : https://prove2.me/theorems/d03bf3ff-b890-4b77-896c-1dac6f62291c
-- title:
--   Cyclotomic: is Open of is Closed of ne zero
-- statement:
--   The Cyclotomic construction uses the is Open of is Closed of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/ClosedSubgroups.lean#L25-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/ClosedSubgroups.lean#L25-L42

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

theorem GroundTheory.Global.Cyclotomic.isOpen_of_isClosed_of_ne_zero (H : AddSubgroup ℤ_[ℓ]) (hH : IsClosed (H : Set ℤ_[ℓ]))
    {x : ℤ_[ℓ]} (hx : x ∈ H) (hx0 : x ≠ 0) : IsOpen (H : Set ℤ_[ℓ]) := by sorry
