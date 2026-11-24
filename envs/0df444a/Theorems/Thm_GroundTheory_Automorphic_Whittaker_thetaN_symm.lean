-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_thetaN_symm
-- name    : GroundTheory.Automorphic.Whittaker.thetaN_symm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:10.577797+00:00
-- url     : https://prove2.me/theorems/649559aa-d965-4569-bff4-e1328534e830
-- title:
--   Whittaker: theta N symm
-- statement:
--   The Whittaker construction uses the theta N symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L249-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L249-L250

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable (ψ₀ : AddChar F ℂ)

theorem GroundTheory.Automorphic.Whittaker.thetaN_symm : (thetaN : Iwasawa.unipotent F n ≃* Iwasawa.unipotent F n).symm = thetaN := by sorry
