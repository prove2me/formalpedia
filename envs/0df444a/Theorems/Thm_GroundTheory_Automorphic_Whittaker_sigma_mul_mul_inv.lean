-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigma_mul_mul_inv
-- name    : GroundTheory.Automorphic.Whittaker.sigma_mul_mul_inv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:34:49.213704+00:00
-- url     : https://prove2.me/theorems/7e6e2e9e-b10a-4ed0-bab6-3e844f011efa
-- title:
--   Whittaker: sigma mul mul inv
-- statement:
--   The Whittaker construction uses the sigma mul mul inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L226-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L226-L228

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

theorem GroundTheory.Automorphic.Whittaker.sigma_mul_mul_inv (a g b : GL (Fin n) F) :
    sigma (a * g * b⁻¹) = theta b * sigma g * (theta a)⁻¹ := by sorry
