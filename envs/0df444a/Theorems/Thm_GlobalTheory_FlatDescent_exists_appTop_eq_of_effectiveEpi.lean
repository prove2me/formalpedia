-- Prove2me | Theorems.Thm_GlobalTheory_FlatDescent_exists_appTop_eq_of_effectiveEpi
-- name    : GlobalTheory.FlatDescent.exists_appTop_eq_of_effectiveEpi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:35:53.338231+00:00
-- url     : https://prove2.me/theorems/348044b0-cdda-4d33-9f00-2bb6e4d58664
-- title:
--   Flat Descent: exists app Top eq of effective Epi
-- statement:
--   The Flat Descent construction uses the exists app Top eq of effective Epi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAppTopEqOfEffectiveEpi.lean#L20-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAppTopEqOfEffectiveEpi.lean#L20-L37

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

theorem GlobalTheory.FlatDescent.exists_appTop_eq_of_effectiveEpi (p : Y ⟶ X) [EffectiveEpi p] {f g : Z ⟶ Y}
    (h : IsPullback f g p p) (s : Γ(Y, ⊤)) (hs : f.appTop s = g.appTop s) :
    ∃ a : Γ(X, ⊤), p.appTop a = s := by sorry
