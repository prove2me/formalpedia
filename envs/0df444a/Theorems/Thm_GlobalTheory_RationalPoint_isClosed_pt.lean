-- Prove2me | Theorems.Thm_GlobalTheory_RationalPoint_isClosed_pt
-- name    : GlobalTheory.RationalPoint.isClosed_pt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:17:55.426829+00:00
-- url     : https://prove2.me/theorems/1f5912e0-70fa-48d4-a935-b07e9e9d65b9
-- title:
--   Rational Point: is Closed pt
-- statement:
--   The Rational Point construction uses the is Closed pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIsClosedImageOfIsClosedSubgroup.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIsClosedImageOfIsClosedSubgroup.lean#L60-L62

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
variable [IsAlgClosed k]

theorem GlobalTheory.RationalPoint.isClosed_pt {X : Over (Sp k)} [LocallyOfFiniteType X.hom] (y : 𝟙_ (Over (Sp k)) ⟶ X) :
    IsClosed {pt y} := by sorry
