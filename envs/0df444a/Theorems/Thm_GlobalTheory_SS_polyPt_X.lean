-- Prove2me | Theorems.Thm_GlobalTheory_SS_polyPt_X
-- name    : GlobalTheory.SS.polyPt_X
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:28:52.376655+00:00
-- url     : https://prove2.me/theorems/aac51a9b-e3b3-4e36-9380-7c77a243ec37
-- title:
--   SS: poly Pt X
-- statement:
--   The SS construction uses the poly Pt X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/OfDerivationFnOn.lean#L333-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/OfDerivationFnOn.lean#L333-L335

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
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
noncomputable section
open GlobalTheory GlobalTheory.SS
variable (R : Type) [CommRing R] {K : Type} [Field K] [Algebra R K]
variable {R} {A A' : Over (Sp K)}

theorem GlobalTheory.SS.polyPt_X {S : Scheme.{0}} {G Z : Over S} [GrpObj G] (F : End G) (x : Z ⟶ G) :
    polyPt F Polynomial.X x = x ≫ (show G ⟶ G from F) := by sorry
