-- Prove2me | Theorems.Thm_GlobalTheory_ThetaSpan_ofIntVec_single
-- name    : GlobalTheory.ThetaSpan.ofIntVec_single
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:53:57.8266+00:00
-- url     : https://prove2.me/theorems/b4eb9413-19ec-48af-a063-7a03fa17d2f1
-- title:
--   Theta Span: of Int Vec single
-- statement:
--   The Theta Span construction uses the of Int Vec single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MemSpanThetaOfLevel.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MemSpanThetaOfLevel.lean#L13-L18

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemSpanThetaOfLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaSpan

theorem GlobalTheory.ThetaSpan.ofIntVec_single {g : ℕ} (j : Fin g) :
    ofIntVec (Pi.single j (1 : ℤ)) = (Pi.single j 1 : Fin g → ℂ) := by sorry
