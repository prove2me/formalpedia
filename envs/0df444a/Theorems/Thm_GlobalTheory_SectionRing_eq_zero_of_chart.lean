-- Prove2me | Theorems.Thm_GlobalTheory_SectionRing_eq_zero_of_chart
-- name    : GlobalTheory.SectionRing.eq_zero_of_chart
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:51:28.143027+00:00
-- url     : https://prove2.me/theorems/b94d335d-2ba7-46ff-86d1-78149cdd1d5e
-- title:
--   Section Ring: eq zero of chart
-- statement:
--   The Section Ring construction uses the eq zero of chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsSectionRing.lean#L176-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsSectionRing.lean#L176-L197

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialMemReesAlgIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsSectionRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SectionRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
variable {K : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K) (L : LB X)

theorem GlobalTheory.SectionRing.eq_zero_of_chart [IsIntegral X] (j₀ : PUnit → L.ι) [Nonempty (chart L j₀)] (e : ℕ)
    (a : Fam p L) (ha : a ∈ secs p L e) (h : evalFam p L j₀ a = 0) : a = 0 := by sorry
