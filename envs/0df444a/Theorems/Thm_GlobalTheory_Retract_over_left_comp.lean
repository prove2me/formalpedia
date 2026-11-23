-- Prove2me | Theorems.Thm_GlobalTheory_Retract_over_left_comp
-- name    : GlobalTheory.Retract.over_left_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:05.707219+00:00
-- url     : https://prove2.me/theorems/fc16c108-70ba-45f0-8cb9-ab85fb7e0068
-- title:
--   Retract: over left comp
-- statement:
--   The Retract construction uses the over left comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L362-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L362-L363

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
variable {S : Scheme.{u}} {X Y : Over S}

theorem GlobalTheory.Retract.over_left_comp (h : CategoryTheory.Retract X Y) : h.i.left ≫ h.r.left = 𝟙 X.left := by sorry
