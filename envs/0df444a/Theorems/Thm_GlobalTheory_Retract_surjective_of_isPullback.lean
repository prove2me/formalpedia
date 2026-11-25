-- Prove2me | Theorems.Thm_GlobalTheory_Retract_surjective_of_isPullback
-- name    : GlobalTheory.Retract.surjective_of_isPullback
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:20:06.300498+00:00
-- url     : https://prove2.me/theorems/a0ae46cd-89ff-4489-bce0-f0ad51936547
-- title:
--   Retract: surjective of is Pullback
-- statement:
--   The Retract construction uses the surjective of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L243-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L243-L245

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory GlobalTheory.Retract
variable {X Y : Scheme.{u}} {i : X ⟶ Y} {r : Y ⟶ X} (hir : i ≫ r = 𝟙 X)
include hir

theorem GlobalTheory.Retract.surjective_of_isPullback {T Z : Scheme.{u}} {t : T ⟶ X} {a : Z ⟶ Y} {r' : Z ⟶ T}
    (h : IsPullback a r' r t) : Surjective r' := by sorry
