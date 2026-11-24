-- Prove2me | Theorems.Thm_GlobalTheory_OriginFrame_rigVal_compat
-- name    : GlobalTheory.OriginFrame.rigVal_compat
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:38:31.314891+00:00
-- url     : https://prove2.me/theorems/dbc0405c-d110-4512-af95-f1593f3c5bc3
-- title:
--   Origin Frame: rig Val compat
-- statement:
--   The Origin Frame construction uses the rig Val compat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsAppellHumbertFrameIsRig.lean#L33-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsAppellHumbertFrameIsRig.lean#L33-L60

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

theorem GlobalTheory.OriginFrame.rigVal_compat (hv : ValRules) {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (L : LB X)
    (rig : LB.Gen (L.pull x)) (hr : rig.IsGen) (j j' : (L.pull x).ι)
    (hj : ⊤ ≤ (L.pull x).U j) (hj' : ⊤ ≤ (L.pull x).U j') :
    valAt' (𝟙 (Sp ℂ)) ((L.pull x).U j) (rig.s j).val =
      valAt' x (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) (L.g (j PUnit.unit) (j' PUnit.unit)).val *
        valAt' (𝟙 (Sp ℂ)) ((L.pull x).U j') (rig.s j').val := by sorry
