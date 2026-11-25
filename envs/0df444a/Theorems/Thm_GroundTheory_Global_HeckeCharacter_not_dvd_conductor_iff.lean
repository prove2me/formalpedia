-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_not_dvd_conductor_iff
-- name    : GroundTheory.Global.HeckeCharacter.not_dvd_conductor_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:49:24.60981+00:00
-- url     : https://prove2.me/theorems/04d1b082-1a99-5958-8690-08b424d902d4
-- title:
--   Hecke Character: not dvd conductor iff
-- statement:
--   The Hecke Character construction uses the not dvd conductor iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeChar.lean#L197-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeChar.lean#L197-L207

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ConductorIdeal
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Theorems.Thm_GroundTheory_Global_IdeleGroup_not_dvd_conductor_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
  FractionalIdeal Function
open scoped NumberField.AdeleRing nonZeroDivisors
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
open GroundTheory.Global.HeckeCharacter
open IdeleGroup
variable (χ : HeckeCharacter K)

theorem GroundTheory.Global.HeckeCharacter.not_dvd_conductor_iff (v : HeightOneSpectrum (𝓞 K)) :
    ¬ v.asIdeal ∣ χ.conductor ↔
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤
        (χ.localComponent v : (v.adicCompletion K)ˣ →* Circle).ker := by sorry
