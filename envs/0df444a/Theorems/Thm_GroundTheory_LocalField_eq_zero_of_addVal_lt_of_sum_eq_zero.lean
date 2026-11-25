-- Prove2me | Theorems.Thm_GroundTheory_LocalField_eq_zero_of_addVal_lt_of_sum_eq_zero
-- name    : GroundTheory.LocalField.eq_zero_of_addVal_lt_of_sum_eq_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:00:30.1778+00:00
-- url     : https://prove2.me/theorems/0d215c1f-d227-482b-b228-1d69c91c5e4d
-- title:
--   Local Field: eq zero of add Val lt of sum eq zero
-- statement:
--   The Local Field construction uses the eq zero of add Val lt of sum eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L17-L27

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem GroundTheory.LocalField.eq_zero_of_addVal_lt_of_sum_eq_zero {ι : Type*} [DecidableEq ι] {s : Finset ι} {t : ι → R}
    (hs : ∑ i ∈ s, t i = 0) {j : ι} (hj : j ∈ s)
    (hlt : ∀ i ∈ s, i ≠ j → addVal R (t j) < addVal R (t i)) : t j = 0 := by sorry
