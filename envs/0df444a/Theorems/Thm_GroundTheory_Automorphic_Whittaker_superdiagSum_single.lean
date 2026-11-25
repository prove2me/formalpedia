-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_superdiagSum_single
-- name    : GroundTheory.Automorphic.Whittaker.superdiagSum_single
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:35:55.390752+00:00
-- url     : https://prove2.me/theorems/2d9a7eee-ab81-4aee-8c1d-73044142bd07
-- title:
--   Whittaker: superdiag Sum single
-- statement:
--   The Whittaker construction uses the superdiag Sum single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L383-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L383-L396

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

theorem GroundTheory.Automorphic.Whittaker.superdiagSum_single (i j : Fin n) (a : F) :
    superdiagSum (Matrix.single i j a) = if j.val = i.val + 1 then a else 0 := by sorry
