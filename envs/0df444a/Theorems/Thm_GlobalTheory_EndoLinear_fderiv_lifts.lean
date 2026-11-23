-- Prove2me | Theorems.Thm_GlobalTheory_EndoLinear_fderiv_lifts
-- name    : GlobalTheory.EndoLinear.fderiv_lifts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:06.035907+00:00
-- url     : https://prove2.me/theorems/2d586f86-88cd-44db-a7a4-be5241aaaf9e
-- title:
--   Endo Linear: fderiv lifts
-- statement:
--   The Endo Linear construction uses the fderiv lifts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsLinearLift.lean#L10-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsLinearLift.lean#L10-L81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearLift
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
open GlobalTheory GlobalTheory.EndoLinear

theorem GlobalTheory.EndoLinear.fderiv_lifts {E E' M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] [Group M] (ex : E' → M) (hex : ∀ z w, ex (z + w) = ex z * ex w)
    (Λ : Submodule ℤ E') (hker : ∀ z, ex z = 1 ↔ z ∈ Λ) (hd : DiscreteTopology Λ)
    (a : E → M) (ha : ∀ z w, a (z + w) = a z * a w) (G : E → E') (h0 : G 0 = 0)
    (hG : DifferentiableAt ℂ G 0) (hev : ∀ᶠ w in 𝓝 0, ex (G w) = a w) (z : E) :
    ex (fderiv ℂ G 0 z) = a z := by sorry
