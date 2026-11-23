-- Prove2me | Theorems.Thm_GlobalTheory_FlatDescent_injective_appTop_of_epi
-- name    : GlobalTheory.FlatDescent.injective_appTop_of_epi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:35:50.257099+00:00
-- url     : https://prove2.me/theorems/1cd7b211-7e65-44f8-8110-fd37756e7998
-- title:
--   Flat Descent: injective app Top of epi
-- statement:
--   The Flat Descent construction uses the injective app Top of epi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAppTopEqOfEffectiveEpi.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAppTopEqOfEffectiveEpi.lean#L13-L18

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

theorem GlobalTheory.FlatDescent.injective_appTop_of_epi (p : Y ⟶ X) [Epi p] : Function.Injective p.appTop := by sorry
