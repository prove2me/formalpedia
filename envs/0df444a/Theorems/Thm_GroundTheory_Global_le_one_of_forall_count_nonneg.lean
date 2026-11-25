-- Prove2me | Theorems.Thm_GroundTheory_Global_le_one_of_forall_count_nonneg
-- name    : GroundTheory.Global.le_one_of_forall_count_nonneg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:14:14.749089+00:00
-- url     : https://prove2.me/theorems/a60eb04d-3fc9-4ef3-945b-e4017a53fa86
-- title:
--   Global: le one of forall count nonneg
-- statement:
--   The Global construction uses the le one of forall count nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L14-L23

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.le_one_of_forall_count_nonneg {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), 0 ≤ count K v I) : I ≤ 1 := by sorry
