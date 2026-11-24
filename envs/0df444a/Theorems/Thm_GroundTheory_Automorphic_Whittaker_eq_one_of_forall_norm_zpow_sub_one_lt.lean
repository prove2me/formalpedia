-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_eq_one_of_forall_norm_zpow_sub_one_lt
-- name    : GroundTheory.Automorphic.Whittaker.eq_one_of_forall_norm_zpow_sub_one_lt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:35:09.818405+00:00
-- url     : https://prove2.me/theorems/58d556a9-75a6-4f45-9a98-42e22f0561da
-- title:
--   Whittaker: eq one of forall norm zpow sub one lt
-- statement:
--   The Whittaker construction uses the eq one of forall norm zpow sub one lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L513-L514
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L513-L514

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Theorems.Thm_P2M_GroundTheory_Variant__N1_eq_one_of_forall_norm_zpow_sub_one_lt_cdf30090e0e9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset

theorem GroundTheory.Automorphic.Whittaker.eq_one_of_forall_norm_zpow_sub_one_lt {z : ℂ} (h : ∀ m : ℤ, ‖z ^ m - 1‖ < 1) : z = 1 := by sorry
