-- Prove2me | Theorems.Thm_GroundTheory_Global_eq_zero_of_forall_infinitePlace_lt_one
-- name    : GroundTheory.Global.eq_zero_of_forall_infinitePlace_lt_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:40:03.983299+00:00
-- url     : https://prove2.me/theorems/8a44adc6-a304-470d-818e-51313d244fb8
-- title:
--   Global: eq zero of forall infinite Place lt one
-- statement:
--   The Global construction uses the eq zero of forall infinite Place lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IntegersLattice.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IntegersLattice.lean#L50-L54

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.AdeleRing
variable (K : Type*) [Field K]
variable [NumberField K]

theorem GroundTheory.Global.eq_zero_of_forall_infinitePlace_lt_one (z : 𝓞 K) (h : ∀ w : InfinitePlace K, w z < 1) :
    z = 0 := by sorry
