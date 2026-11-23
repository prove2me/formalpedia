-- Prove2me | Theorems.Thm_GlobalTheory_Retract_locallyOfFiniteType
-- name    : GlobalTheory.Retract.locallyOfFiniteType
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:14.521805+00:00
-- url     : https://prove2.me/theorems/27233539-cfe8-4c86-8a4e-7f4a37f1e844
-- title:
--   Retract: locally Of Finite Type
-- statement:
--   The Retract construction uses the locally Of Finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L197-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L197-L200

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

theorem GlobalTheory.Retract.locallyOfFiniteType [hg : LocallyOfFiniteType g] : LocallyOfFiniteType f := by sorry
