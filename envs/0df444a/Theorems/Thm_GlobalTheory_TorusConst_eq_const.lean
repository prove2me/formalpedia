-- Prove2me | Theorems.Thm_GlobalTheory_TorusConst_eq_const
-- name    : GlobalTheory.TorusConst.eq_const
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:09:47.380806+00:00
-- url     : https://prove2.me/theorems/b7d188c8-df46-47b4-b5be-46b68ea125d9
-- title:
--   Torus Const: eq const
-- statement:
--   The Torus Const construction uses the eq const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L428-L474
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L428-L474

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusConst
open Polynomial TorusToProper
variable {K : Type} [Field K] {B : Over (Spec (CommRingCat.of K))}

theorem GlobalTheory.TorusConst.eq_const (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] [GrpObj B]
    [IsProper B.hom] (f : splitTorus (Spec (CommRingCat.of K)) Y ⟶ B) :
    f = toUnit _ ≫ η ≫ f := by sorry
