-- Prove2me | Theorems.Thm_GlobalTheory_TorusEnd_exists_top_le_preimage_of_iSup_eq_top
-- name    : GlobalTheory.TorusEnd.exists_top_le_preimage_of_iSup_eq_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:22:05.749082+00:00
-- url     : https://prove2.me/theorems/d38b7ca6-19fc-4517-b04b-da18ba29e836
-- title:
--   Torus End: exists top le preimage of i Sup eq top
-- statement:
--   The Torus End construction uses the exists top le preimage of i Sup eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsTopLePreimageOfISupEqTop.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsTopLePreimageOfISupEqTop.lean#L25-L29

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

theorem GlobalTheory.TorusEnd.exists_top_le_preimage_of_iSup_eq_top {X : Scheme.{0}} {κ : Type*} (x : Sp ℂ ⟶ X) (U : κ → X.Opens)
    (h : ⨆ i, U i = ⊤) : ∃ i, ⊤ ≤ x ⁻¹ᵁ U i := by sorry
