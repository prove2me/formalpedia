-- Prove2me | Theorems.Thm_GlobalTheory_ComplexPointsGroup_IsContFamily_continuousOn
-- name    : GlobalTheory.ComplexPointsGroup.IsContFamily.continuousOn
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:25:38.330802+00:00
-- url     : https://prove2.me/theorems/40e9ac00-018f-4a91-981e-b80004ddf409
-- title:
--   Is Cont Family: continuous On
-- statement:
--   The Is Cont Family construction uses the continuous On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsTopologicalGroupComplexPoints.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsTopologicalGroupComplexPoints.lean#L20-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsTopologicalGroupComplexPoints
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
open GlobalTheory GlobalTheory.ComplexPointsGroup
variable {T : Type} [TopologicalSpace T]

theorem GlobalTheory.ComplexPointsGroup.IsContFamily.continuousOn {X : Scheme.{0}} {e : T → (Sp ℂ ⟶ X)} (he : IsContFamily e) (U : X.Opens)
    (f : Γ(X, U)) : ContinuousOn (fun t => valAt' (e t) U f) {t | ⊤ ≤ e t ⁻¹ᵁ U} := by sorry
