-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_infiniteComponent_apply
-- name    : GroundTheory.Global.HeckeCharacter.infiniteComponent_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:55:20.064574+00:00
-- url     : https://prove2.me/theorems/5a41f55c-cb3e-5a2e-9a9c-2745756a51fb
-- title:
--   Hecke Character: infinite Component apply
-- statement:
--   The Hecke Character construction uses the infinite Component apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeChar.lean#L180-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeChar.lean#L180-L182

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

theorem GroundTheory.Global.HeckeCharacter.infiniteComponent_apply (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    χ.infiniteComponent w a = χ.toIdele (infiniteEmbedding w a) := by sorry
