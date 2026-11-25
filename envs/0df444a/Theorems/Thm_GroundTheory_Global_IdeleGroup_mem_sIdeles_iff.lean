-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_sIdeles_iff
-- name    : GroundTheory.Global.IdeleGroup.mem_sIdeles_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:59.279894+00:00
-- url     : https://prove2.me/theorems/2566ffad-e0d9-5bbd-a828-79113c25551f
-- title:
--   Idele Group: mem s Ideles iff
-- statement:
--   The Idele Group construction uses the mem s Ideles iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/SIdeleGroups.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/SIdeleGroups.lean#L26-L29

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

theorem GroundTheory.Global.IdeleGroup.mem_sIdeles_iff {x : IdeleGroup K} :
    x ∈ sIdeles S ↔ ∀ v ∉ S, (x : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K ∧
      ((x⁻¹ : IdeleGroup K) : 𝔸[K]).2 v ∈ v.adicCompletionIntegers K := by sorry
