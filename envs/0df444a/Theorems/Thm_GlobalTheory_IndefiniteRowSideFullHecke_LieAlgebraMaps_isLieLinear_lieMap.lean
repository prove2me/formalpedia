-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LieAlgebraMaps_isLieLinear_lieMap
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.isLieLinear_lieMap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:01.615086+00:00
-- url     : https://prove2.me/theorems/aa113048-47ee-4ad3-9463-7aa017431c14
-- title:
--   Lie Algebra Maps: is Lie Linear lie Map
-- statement:
--   The Lie Algebra Maps construction uses the is Lie Linear lie Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/LieAlgebraMaps.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/LieAlgebraMaps.lean#L70-L73

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LieAlgebraMaps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps

theorem GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.isLieLinear_lieMap {R : Type} [CommRing R] {T G : Over (Spec (CommRingCat.of R))}
    [GrpObj T] [GrpObj G] (u : T ⟶ G) [IsMonHom u] : IsLieLinear (lieMap u) := by sorry
