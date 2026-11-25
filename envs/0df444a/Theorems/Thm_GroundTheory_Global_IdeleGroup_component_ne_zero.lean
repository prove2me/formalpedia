-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_component_ne_zero
-- name    : GroundTheory.Global.IdeleGroup.component_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:17:54.620584+00:00
-- url     : https://prove2.me/theorems/6ddcfc2c-9479-42b1-986d-ad4a6d1b468c
-- title:
--   Idele Group: component ne zero
-- statement:
--   The Idele Group construction uses the component ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L155-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L155-L157

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
open GroundTheory.Global.IdeleGroup
local notation "𝓘" => (FractionalIdeal (𝓞 K)⁰ K)ˣ

theorem GroundTheory.Global.IdeleGroup.component_ne_zero (v : HeightOneSpectrum (𝓞 K)) (s : IdeleGroup K) :
    (s : 𝔸[K]).2 v ≠ 0 := by sorry
