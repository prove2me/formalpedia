-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_sUnitsToSIdeles_injective
-- name    : GroundTheory.Global.IdeleGroup.sUnitsToSIdeles_injective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:18:42.707445+00:00
-- url     : https://prove2.me/theorems/a84a0204-9eb8-41b3-8910-49c59bd2d8ce
-- title:
--   Idele Group: s Units To SIdeles injective
-- statement:
--   The Idele Group construction uses the s Units To SIdeles injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/SIdeleGroups.lean#L98-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/SIdeleGroups.lean#L98-L99

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

theorem GroundTheory.Global.IdeleGroup.sUnitsToSIdeles_injective : Function.Injective (sUnitsToSIdeles S) := by sorry
