-- Prove2me | Theorems.Thm_GlobalTheory_RationalPoint_isConstructible_image_of_isClosed
-- name    : GlobalTheory.RationalPoint.isConstructible_image_of_isClosed
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:15:10.786462+00:00
-- url     : https://prove2.me/theorems/659ec216-a7de-48dc-a009-10d461baec56
-- title:
--   Rational Point: is Constructible image of is Closed
-- statement:
--   The Rational Point construction uses the is Constructible image of is Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIsClosedImageOfIsClosedSubgroup.lean#L92-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIsClosedImageOfIsClosedSubgroup.lean#L92-L106

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
omit [IsAlgClosed k]

theorem GlobalTheory.RationalPoint.isConstructible_image_of_isClosed {X Y : Over (Sp k)} [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (f : X ⟶ Y)
    {Z : Set X.left} (hZ : IsClosed Z) : IsConstructible (f.left '' Z) := by sorry
