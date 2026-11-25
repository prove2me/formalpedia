-- Prove2me | Theorems.Thm_GlobalTheory_LieChart_exists_chart_pullback
-- name    : GlobalTheory.LieChart.exists_chart_pullback
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:58:10.851134+00:00
-- url     : https://prove2.me/theorems/4c4f824e-7113-5713-9719-25cf2b10194a
-- title:
--   Lie Chart: exists chart pullback
-- statement:
--   The Lie Chart construction uses the exists chart pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsAffineLieBasisBaseChange.lean#L221-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsAffineLieBasisBaseChange.lean#L221-L248

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

theorem GlobalTheory.LieChart.exists_chart_pullback {X : Scheme.{0}} (G : Over X) [GrpObj G] {U : X.Opens} (hU : IsAffineOpen U)
    {V : G.left.Opens} (hV : IsAffineOpen V) (e : V ≤ G.hom ⁻¹ᵁ U) (hs : U ≤ (η[G]).left ⁻¹ᵁ V)
    (h : (G.hom.appLE U V e).hom.IsStandardSmooth) (G₀ : Over (Spec (CommRingCat.of Γ(X, U)))) [GrpObj G₀]
    (φ : G₀.left ⟶ G.left) (hφ : IsGrpPullback G₀ G hU.fromSpec φ) :
    ∃ C : Chart G₀, (alg0 C).IsStandardSmooth := by sorry
