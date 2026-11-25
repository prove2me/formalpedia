-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigmaMat_eq
-- name    : GroundTheory.Automorphic.Whittaker.sigmaMat_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:35:06.128186+00:00
-- url     : https://prove2.me/theorems/480dcae6-e240-4640-be70-3b4b75192c71
-- title:
--   Whittaker: sigma Mat eq
-- statement:
--   The Whittaker construction uses the sigma Mat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L136-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L136-L141

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

theorem GroundTheory.Automorphic.Whittaker.sigmaMat_eq (M : Matrix (Fin n) (Fin n) F) :
    sigmaMat M = ((permGL F (Fin.revPerm (n := n)) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * Mᵀ *
      ((permGL F (Fin.revPerm (n := n)) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by sorry
