-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_localComponent_uniformizer_eq
-- name    : GroundTheory.Global.HeckeCharacter.localComponent_uniformizer_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:01:04.164357+00:00
-- url     : https://prove2.me/theorems/acae9ffb-ef05-4752-acd1-90c30755ce61
-- title:
--   Hecke Character: local Component uniformizer eq
-- statement:
--   The Hecke Character construction uses the local Component uniformizer eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeChar.lean#L215-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeChar.lean#L215-L230

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

theorem GroundTheory.Global.HeckeCharacter.localComponent_uniformizer_eq {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ χ.conductor) {π π' : (v.adicCompletion K)ˣ}
    (hπ : Valued.v (π : v.adicCompletion K) = exp (-1 : ℤ))
    (hπ' : Valued.v (π' : v.adicCompletion K) = exp (-1 : ℤ)) :
    χ.localComponent v π = χ.localComponent v π' := by sorry
