-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_toIdele_diagonal
-- name    : GroundTheory.Global.HeckeCharacter.toIdele_diagonal
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:12:21.828941+00:00
-- url     : https://prove2.me/theorems/c5f397d9-a42e-4ed6-9187-5be04c982a19
-- title:
--   Hecke Character: to Idele diagonal
-- statement:
--   The Hecke Character construction uses the to Idele diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeChar.lean#L165-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeChar.lean#L165-L166

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

theorem GroundTheory.Global.HeckeCharacter.toIdele_diagonal (a : Kˣ) : χ.toIdele (diagonal K a) = 1 := by sorry
