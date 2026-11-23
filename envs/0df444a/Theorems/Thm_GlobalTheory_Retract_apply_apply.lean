-- Prove2me | Theorems.Thm_GlobalTheory_Retract_apply_apply
-- name    : GlobalTheory.Retract.apply_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:24.436884+00:00
-- url     : https://prove2.me/theorems/c293eb13-1f5b-422a-93dd-c98d59d85c7a
-- title:
--   Retract: apply apply
-- statement:
--   The Retract construction uses the apply apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L85-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L85-L86

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

theorem GlobalTheory.Retract.apply_apply (hir : i ≫ r = 𝟙 X) (x : X) : r (i x) = x := by sorry
