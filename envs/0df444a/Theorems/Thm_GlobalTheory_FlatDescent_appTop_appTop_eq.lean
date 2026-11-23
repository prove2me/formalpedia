-- Prove2me | Theorems.Thm_GlobalTheory_FlatDescent_appTop_appTop_eq
-- name    : GlobalTheory.FlatDescent.appTop_appTop_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:35:44.57485+00:00
-- url     : https://prove2.me/theorems/ee8f7558-9c6c-450a-8fee-19b9339125e6
-- title:
--   Flat Descent: app Top app Top eq
-- statement:
--   The Flat Descent construction uses the app Top app Top eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAppTopEqOfEffectiveEpi.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAppTopEqOfEffectiveEpi.lean#L39-L42

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

theorem GlobalTheory.FlatDescent.appTop_appTop_eq {p : Y ⟶ X} {f g : Z ⟶ Y} (h : f ≫ p = g ≫ p) (a : Γ(X, ⊤)) :
    f.appTop (p.appTop a) = g.appTop (p.appTop a) := by sorry
