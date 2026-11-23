-- Prove2me | Theorems.Thm_GlobalTheory_TangentOrigin_eq_spec_fromSpec
-- name    : GlobalTheory.TangentOrigin.eq_spec_fromSpec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:39.567032+00:00
-- url     : https://prove2.me/theorems/854cf520-7e10-4ba2-9cb4-59011c2dec0f
-- title:
--   Tangent Origin: eq spec from Spec
-- statement:
--   The Tangent Origin construction uses the eq spec from Spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L37-L43

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

theorem GlobalTheory.TangentOrigin.eq_spec_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (x : Sp R ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    x = Spec.map (CommRingCat.ofHom (evalPt x U h)) ≫ hU.fromSpec := by sorry
