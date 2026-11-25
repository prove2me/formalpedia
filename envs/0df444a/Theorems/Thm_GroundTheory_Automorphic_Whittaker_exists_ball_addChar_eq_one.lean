-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_ball_addChar_eq_one
-- name    : GroundTheory.Automorphic.Whittaker.exists_ball_addChar_eq_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:35:59.016599+00:00
-- url     : https://prove2.me/theorems/7d55e0e9-dab5-4e11-864d-de604aef0d72
-- title:
--   Whittaker: exists ball add Char eq one
-- statement:
--   The Whittaker construction uses the exists ball add Char eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L523-L539
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L523-L539

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
open ValuativeRel Topology
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)

theorem GroundTheory.Automorphic.Whittaker.exists_ball_addChar_eq_one {ψ₀ : AddChar F ℂ} (hψ : Continuous ψ₀) :
    ∃ γ : (ValueGroupWithZero F)ˣ, ∀ x : F, valuation F x < γ → ψ₀ x = 1 := by sorry
