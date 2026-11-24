-- Prove2me | Theorems.Thm_GlobalTheory_RationalPoint_pt_injective
-- name    : GlobalTheory.RationalPoint.pt_injective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:15:33.799528+00:00
-- url     : https://prove2.me/theorems/9843390d-df5b-45eb-bd89-91133454cbd8
-- title:
--   Rational Point: pt injective
-- statement:
--   The Rational Point construction uses the pt injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIsClosedImageOfIsClosedSubgroup.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIsClosedImageOfIsClosedSubgroup.lean#L64-L66

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

theorem GlobalTheory.RationalPoint.pt_injective {X : Over (Sp k)} [LocallyOfFiniteType X.hom] :
    Function.Injective (pt : (𝟙_ (Over (Sp k)) ⟶ X) → X.left) := by sorry
