-- Prove2me | Theorems.Thm_GlobalTheory_TangentOrigin_ext_evalPt
-- name    : GlobalTheory.TangentOrigin.ext_evalPt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:39.957381+00:00
-- url     : https://prove2.me/theorems/13cd6ee2-bff9-4403-b545-989b0069faea
-- title:
--   Tangent Origin: ext eval Pt
-- statement:
--   The Tangent Origin construction uses the ext eval Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L45-L47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.TangentOrigin
variable {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}

theorem GlobalTheory.TangentOrigin.ext_evalPt {U : X.Opens} (hU : IsAffineOpen U) {x y : Sp R ⟶ X} (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (hy : ⊤ ≤ y ⁻¹ᵁ U) (e : evalPt x U hx = evalPt y U hy) : x = y := by sorry
