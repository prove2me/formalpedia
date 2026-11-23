-- Prove2me | Theorems.Thm_GlobalTheory_FlatDescent_isUnit_appTop_iff
-- name    : GlobalTheory.FlatDescent.isUnit_appTop_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:44.137848+00:00
-- url     : https://prove2.me/theorems/4b9f2260-79fa-4efd-a497-05389da6d964
-- title:
--   Flat Descent: is Unit app Top iff
-- statement:
--   The Flat Descent construction uses the is Unit app Top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAppTopEqOfEffectiveEpi.lean#L53-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAppTopEqOfEffectiveEpi.lean#L53-L64

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

theorem GlobalTheory.FlatDescent.isUnit_appTop_iff (p : Y ⟶ X) [EffectiveEpi p] (a : Γ(X, ⊤)) :
    IsUnit (p.appTop a) ↔ IsUnit a := by sorry
