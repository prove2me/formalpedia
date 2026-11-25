-- Prove2me | Theorems.Thm_GlobalTheory_TorusExt_iota_val
-- name    : GlobalTheory.TorusExt.iota_val
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:41:32.109001+00:00
-- url     : https://prove2.me/theorems/3b2cf23c-1de6-4154-85dd-3e6e6a43f4b1
-- title:
--   Torus Ext: iota val
-- statement:
--   The Torus Ext construction uses the iota val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsNsmulIffEq.lean#L293-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsNsmulIffEq.lean#L293-L294

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

theorem GlobalTheory.TorusExt.iota_val (hB : D.TauBimult) (x χ : D.X) {y J} (hJ : Good D.P.L y J) :
    charVal (iota hB F x) χ y J = tauVal D F x χ y J := by sorry
