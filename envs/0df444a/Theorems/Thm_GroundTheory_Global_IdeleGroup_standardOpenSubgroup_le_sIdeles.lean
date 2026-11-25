-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroup_le_sIdeles
-- name    : GroundTheory.Global.IdeleGroup.standardOpenSubgroup_le_sIdeles
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:40:41.147593+00:00
-- url     : https://prove2.me/theorems/66297e94-f0d0-470e-a402-10ddce83b823
-- title:
--   Idele Group: standard Open Subgroup le s Ideles
-- statement:
--   The Idele Group construction uses the standard Open Subgroup le s Ideles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/SIdeleGroups.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/SIdeleGroups.lean#L31-L32

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups
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
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable (S : Set (HeightOneSpectrum (𝓞 K)))

theorem GroundTheory.Global.IdeleGroup.standardOpenSubgroup_le_sIdeles : standardOpenSubgroup K ≤ sIdeles S := by sorry
