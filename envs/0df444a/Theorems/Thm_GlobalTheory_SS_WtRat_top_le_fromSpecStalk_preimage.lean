-- Prove2me | Theorems.Thm_GlobalTheory_SS_WtRat_top_le_fromSpecStalk_preimage
-- name    : GlobalTheory.SS.WtRat.top_le_fromSpecStalk_preimage
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:37:52.166975+00:00
-- url     : https://prove2.me/theorems/b3c01ddb-ccc7-4269-ab04-86eda8f2a97d
-- title:
--   Wt Rat: top le from Spec Stalk preimage
-- statement:
--   The Wt Rat construction uses the top le from Spec Stalk preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsGenericFunctionFieldPoint.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsGenericFunctionFieldPoint.lean#L15-L20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGenericFunctionFieldPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WtRat
variable {Y : Scheme.{0}}

theorem GlobalTheory.SS.WtRat.top_le_fromSpecStalk_preimage (x : Y) {V : Y.Opens} (hx : x ∈ V) :
    ⊤ ≤ Y.fromSpecStalk x ⁻¹ᵁ V := by sorry
