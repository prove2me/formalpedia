-- Prove2me | Theorems.Thm_GlobalTheory_TangentOrigin_exists_evalPt_eq
-- name    : GlobalTheory.TangentOrigin.exists_evalPt_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:24.824703+00:00
-- url     : https://prove2.me/theorems/d182a3ea-86ac-40e5-9c5e-5a4d1ff153a6
-- title:
--   Tangent Origin: exists eval Pt eq
-- statement:
--   The Tangent Origin construction uses the exists eval Pt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L49-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L49-L58

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

theorem GlobalTheory.TangentOrigin.exists_evalPt_eq {U : X.Opens} (hU : IsAffineOpen U) (ψ : Γ(X, U) →+* R) :
    ∃ (x : Sp R ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U), evalPt x U h = ψ := by sorry
