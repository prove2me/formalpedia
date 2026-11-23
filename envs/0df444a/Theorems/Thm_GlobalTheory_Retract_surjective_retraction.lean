-- Prove2me | Theorems.Thm_GlobalTheory_Retract_surjective_retraction
-- name    : GlobalTheory.Retract.surjective_retraction
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:49.98765+00:00
-- url     : https://prove2.me/theorems/e3946176-7b1c-456e-98df-9f3d7abf6f1a
-- title:
--   Retract: surjective retraction
-- statement:
--   The Retract construction uses the surjective retraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L240-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L240-L241

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

theorem GlobalTheory.Retract.surjective_retraction : Surjective r := by sorry
