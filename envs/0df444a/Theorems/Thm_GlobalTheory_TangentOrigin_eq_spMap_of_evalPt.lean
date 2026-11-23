-- Prove2me | Theorems.Thm_GlobalTheory_TangentOrigin_eq_spMap_of_evalPt
-- name    : GlobalTheory.TangentOrigin.eq_spMap_of_evalPt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:34.929033+00:00
-- url     : https://prove2.me/theorems/90c6771c-8293-4c02-8351-3fcfab00ea10
-- title:
--   Tangent Origin: eq sp Map of eval Pt
-- statement:
--   The Tangent Origin construction uses the eq sp Map of eval Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L80-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TangentBijectionOfValues.lean#L80-L86

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

theorem GlobalTheory.TangentOrigin.eq_spMap_of_evalPt {k : Type} [CommRing k] (y : Sp R ⟶ Sp k) (φ : k →+* R)
    (h : ∀ a, evalPt y ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a) = φ a) :
    y = spMap φ := by sorry
