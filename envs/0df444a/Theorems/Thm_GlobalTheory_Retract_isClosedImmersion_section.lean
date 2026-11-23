-- Prove2me | Theorems.Thm_GlobalTheory_Retract_isClosedImmersion_section
-- name    : GlobalTheory.Retract.isClosedImmersion_section
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:06.274605+00:00
-- url     : https://prove2.me/theorems/92e44db3-becf-4af4-8efb-5e17cacb6ce5
-- title:
--   Retract: is Closed Immersion section
-- statement:
--   The Retract construction uses the is Closed Immersion section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L276-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L276-L280

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
  (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g)
include hir hr

theorem GlobalTheory.Retract.isClosedImmersion_section [IsSeparated g] : IsClosedImmersion i := by sorry
