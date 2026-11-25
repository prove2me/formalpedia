-- Prove2me | Theorems.Thm_GlobalTheory_FlatDescent_isUnit_app_iff
-- name    : GlobalTheory.FlatDescent.isUnit_app_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:05:19.22164+00:00
-- url     : https://prove2.me/theorems/64fa4f9f-4402-41bf-a468-6683a86aeb15
-- title:
--   Flat Descent: is Unit app iff
-- statement:
--   The Flat Descent construction uses the is Unit app iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAppTopEqOfEffectiveEpi.lean#L139-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAppTopEqOfEffectiveEpi.lean#L139-L143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory
open GlobalTheory.FlatDescent
universe u
variable {X Y Z : Scheme.{u}}

theorem GlobalTheory.FlatDescent.isUnit_app_iff (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p] (U : X.Opens)
    (a : Γ(X, U)) : IsUnit (p.app U a) ↔ IsUnit a := by sorry
