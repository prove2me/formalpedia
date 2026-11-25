-- Prove2me | Theorems.Thm_GlobalTheory_RationalPoint_pt_comp
-- name    : GlobalTheory.RationalPoint.pt_comp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:03.688858+00:00
-- url     : https://prove2.me/theorems/8937cd20-5698-46a0-b605-8ea57fcd9a45
-- title:
--   Rational Point: pt comp
-- statement:
--   The Rational Point construction uses the pt comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIsClosedImageOfIsClosedSubgroup.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIsClosedImageOfIsClosedSubgroup.lean#L27-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Topology
open GlobalTheory
open GlobalTheory.RationalPoint
variable {k : Type} [Field k]

theorem GlobalTheory.RationalPoint.pt_comp {X Y : Over (Sp k)} (y : 𝟙_ (Over (Sp k)) ⟶ X) (f : X ⟶ Y) :
    pt (y ≫ f) = f.left (pt y) := by sorry
