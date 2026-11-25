-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_sIdeles_mono
-- name    : GroundTheory.Global.IdeleGroup.sIdeles_mono
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:13:35.709877+00:00
-- url     : https://prove2.me/theorems/980f963c-677d-4ad2-a293-4871e424a444
-- title:
--   Idele Group: s Ideles mono
-- statement:
--   The Idele Group construction uses the s Ideles mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/SIdeleGroups.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/SIdeleGroups.lean#L34-L36

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

theorem GroundTheory.Global.IdeleGroup.sIdeles_mono {S T : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) :
    sIdeles S ≤ sIdeles T := by sorry
