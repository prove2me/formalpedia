-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigma_mem_unipotent_iff
-- name    : GroundTheory.Automorphic.Whittaker.sigma_mem_unipotent_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:53:20.183887+00:00
-- url     : https://prove2.me/theorems/930f7cd2-bc47-50ab-b4fd-e586194022b3
-- title:
--   Whittaker: sigma mem unipotent iff
-- statement:
--   The Whittaker construction uses the sigma mem unipotent iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L199-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L199-L201

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

theorem GroundTheory.Automorphic.Whittaker.sigma_mem_unipotent_iff {u : GL (Fin n) F} :
    sigma u ∈ Iwasawa.unipotent F n ↔ u ∈ Iwasawa.unipotent F n := by sorry
