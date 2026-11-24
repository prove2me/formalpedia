-- Prove2me | Theorems.Thm_GlobalTheory_TorusEnd_top_le_preimage_finset_inf
-- name    : GlobalTheory.TorusEnd.top_le_preimage_finset_inf
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:10:15.439546+00:00
-- url     : https://prove2.me/theorems/40264bd2-fb57-4bc3-8e21-b8040dd5d240
-- title:
--   Torus End: top le preimage finset inf
-- statement:
--   The Torus End construction uses the top le preimage finset inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsTopLePreimageOfISupEqTop.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsTopLePreimageOfISupEqTop.lean#L18-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTopLePreimageOfISupEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.TorusEnd

theorem GlobalTheory.TorusEnd.top_le_preimage_finset_inf {X : Scheme.{0}} {κ : Type*} (x : Sp ℂ ⟶ X) (s : Finset κ) (U : κ → X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ (s.inf U) ↔ ∀ i ∈ s, ⊤ ≤ x ⁻¹ᵁ U i := by sorry
