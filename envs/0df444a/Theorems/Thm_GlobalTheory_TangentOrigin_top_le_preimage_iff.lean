-- Prove2me | Theorems.Thm_GlobalTheory_TangentOrigin_top_le_preimage_iff
-- name    : GlobalTheory.TangentOrigin.top_le_preimage_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:49.982627+00:00
-- url     : https://prove2.me/theorems/6c76cca3-1d19-421a-a9a4-379a45513556
-- title:
--   Tangent Origin: top le preimage iff
-- statement:
--   The Tangent Origin construction uses the top le preimage iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L115-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L115-L122

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

theorem GlobalTheory.TangentOrigin.top_le_preimage_iff (x : Sp (DualNumber ℂ) ⟶ X) (W : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ W ↔ ⊤ ≤ (spMap fstC ≫ x) ⁻¹ᵁ W := by sorry
