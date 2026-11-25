-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_localComponent_apply
-- name    : GroundTheory.Global.HeckeCharacter.localComponent_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:55:20.680056+00:00
-- url     : https://prove2.me/theorems/18764025-6e59-5d2e-ac72-eab5528d2108
-- title:
--   Hecke Character: local Component apply
-- statement:
--   The Hecke Character construction uses the local Component apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeChar.lean#L172-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeChar.lean#L172-L174

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

theorem GroundTheory.Global.HeckeCharacter.localComponent_apply (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    χ.localComponent v a = χ.toIdele (finiteEmbedding v a) := by sorry
