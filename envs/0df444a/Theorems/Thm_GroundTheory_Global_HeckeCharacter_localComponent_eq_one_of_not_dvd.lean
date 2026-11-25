-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_localComponent_eq_one_of_not_dvd
-- name    : GroundTheory.Global.HeckeCharacter.localComponent_eq_one_of_not_dvd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:49:16.799156+00:00
-- url     : https://prove2.me/theorems/ca2cfd29-cafd-5e2d-9346-077668fc8b59
-- title:
--   Hecke Character: local Component eq one of not dvd
-- statement:
--   The Hecke Character construction uses the local Component eq one of not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeChar.lean#L209-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeChar.lean#L209-L213

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ConductorIdeal
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
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

theorem GroundTheory.Global.HeckeCharacter.localComponent_eq_one_of_not_dvd {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ χ.conductor) {a : (v.adicCompletion K)ˣ}
    (ha : a ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units) :
    χ.localComponent v a = 1 := by sorry
