-- Prove2me | Theorems.Thm_GlobalTheory_OriginFrame_rigVal_ne_zero
-- name    : GlobalTheory.OriginFrame.rigVal_ne_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:38:30.497953+00:00
-- url     : https://prove2.me/theorems/6ca2b3ab-5812-4054-9f5f-696fd610052e
-- title:
--   Origin Frame: rig Val ne zero
-- statement:
--   The Origin Frame construction uses the rig Val ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsAppellHumbertFrameIsRig.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsAppellHumbertFrameIsRig.lean#L16-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsAppellHumbertFrameIsRig
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
open GlobalTheory
open GlobalTheory.OriginFrame

theorem GlobalTheory.OriginFrame.rigVal_ne_zero (hv : ValRules) {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (s : Γ(X, U)ˣ) : valAt' x U s.val ≠ 0 := by sorry
