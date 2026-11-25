-- Prove2me | Theorems.Thm_GlobalTheory_LieChart_univChart_of_chart
-- name    : GlobalTheory.LieChart.univChart_of_chart
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:59:44.490567+00:00
-- url     : https://prove2.me/theorems/b9675804-64f4-5fb7-a24e-7a24b2aab15f
-- title:
--   Lie Chart: univ Chart of chart
-- statement:
--   The Lie Chart construction uses the univ Chart of chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsAffineLieBasisBaseChange.lean#L79-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsAffineLieBasisBaseChange.lean#L79-L99

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsAffineLieBasisBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LieChart
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp
open scoped CategoryTheory.Obj

theorem GlobalTheory.LieChart.univChart_of_chart {R : Type} [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (C : Chart G)
    (hC : (alg0 C).IsStandardSmooth) :
    ∃ (d : ℕ) (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), IsUnivChart G d x := by sorry
