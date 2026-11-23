-- Prove2me | Theorems.Thm_GlobalTheory_FlatDescent_appTop_resLE_apply
-- name    : GlobalTheory.FlatDescent.appTop_resLE_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:46.889379+00:00
-- url     : https://prove2.me/theorems/01ffd85a-1486-45d5-a42d-b5e4c254eac4
-- title:
--   Flat Descent: app Top res LE apply
-- statement:
--   The Flat Descent construction uses the app Top res LE apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAppTopEqOfEffectiveEpi.lean#L107-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAppTopEqOfEffectiveEpi.lean#L107-L111

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

theorem GlobalTheory.FlatDescent.appTop_resLE_apply (f : Z ⟶ Y) (V : Y.Opens) (W : Z.Opens) (e : W ≤ f ⁻¹ᵁ V)
    (s : Γ(Y, V)) : (f.resLE V W e).appTop (V.topIso.inv s) = W.topIso.inv (f.appLE V W e s) := by sorry
