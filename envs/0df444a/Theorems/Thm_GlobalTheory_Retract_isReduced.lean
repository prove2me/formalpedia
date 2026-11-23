-- Prove2me | Theorems.Thm_GlobalTheory_Retract_isReduced
-- name    : GlobalTheory.Retract.isReduced
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:42.807609+00:00
-- url     : https://prove2.me/theorems/c84c86d9-12e7-42c4-89b5-59b8d21aac00
-- title:
--   Retract: is Reduced
-- statement:
--   The Retract construction uses the is Reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L256-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L256-L263

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

theorem GlobalTheory.Retract.isReduced [IsReduced Y] : IsReduced X := by sorry
