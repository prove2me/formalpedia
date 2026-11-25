-- Prove2me | Theorems.Thm_GlobalTheory_TorusExt_add_val
-- name    : GlobalTheory.TorusExt.add_val
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:02:05.934857+00:00
-- url     : https://prove2.me/theorems/725434d3-c820-5aa7-92bf-106691a01d6b
-- title:
--   Torus Ext: add val
-- statement:
--   The Torus Ext construction uses the add val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsNsmulIffEq.lean#L235-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsNsmulIffEq.lean#L235-L236

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TorusExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
attribute [local instance] gtGroup

theorem GlobalTheory.TorusExt.add_val (g g' : GtPtF D F) (χ : D.X) {y J} (hJ : Good D.P.L y J) :
    charVal (g + g') χ y J * th D y J (cP D _ χ) g.b g'.b = charVal g χ y J * charVal g' χ y J := by sorry
