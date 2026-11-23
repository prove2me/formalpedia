-- Prove2me | Theorems.Thm_GlobalTheory_HolChart_exists_etale_coords_vanishing
-- name    : GlobalTheory.HolChart.exists_etale_coords_vanishing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:58:37.309083+00:00
-- url     : https://prove2.me/theorems/ea409a80-a55e-42d7-b9b5-f01035bb2650
-- title:
--   Hol Chart: exists etale coords vanishing
-- statement:
--   The Hol Chart construction uses the exists etale coords vanishing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsEtaleCoordsVanishing.lean#L13-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsEtaleCoordsVanishing.lean#L13-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing
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
open GlobalTheory GlobalTheory.HolChart

theorem GlobalTheory.HolChart.exists_etale_coords_vanishing {g : ℕ} {A : Type} [CommRing A] (c : ℂ →+* A)
    (hc : c.IsStandardSmoothOfRelativeDimension g) (e : A →+* ℂ) (he : ∀ a, e (c a) = a) :
    ∃ φ : MvPolynomial (Fin g) ℂ →+* A, φ.comp MvPolynomial.C = c ∧ φ.Etale ∧
      ∀ i, e (φ (MvPolynomial.X i)) = 0 := by sorry
