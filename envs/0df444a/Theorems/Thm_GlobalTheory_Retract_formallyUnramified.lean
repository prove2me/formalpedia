-- Prove2me | Theorems.Thm_GlobalTheory_Retract_formallyUnramified
-- name    : GlobalTheory.Retract.formallyUnramified
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:19:44.704415+00:00
-- url     : https://prove2.me/theorems/0af29764-0b41-5aac-803e-d701ba59344e
-- title:
--   Retract: formally Unramified
-- statement:
--   The Retract construction uses the formally Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L223-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L223-L226

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
variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {i : X ⟶ Y} {r : Y ⟶ X}
variable (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g)
include hir hr

theorem GlobalTheory.Retract.formallyUnramified [hg : FormallyUnramified g] : FormallyUnramified f := by sorry
