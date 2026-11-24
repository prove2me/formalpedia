-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_seriesEval_subst
-- name    : GroundTheory.PAdicHodge.seriesEval_subst
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:37.419511+00:00
-- url     : https://prove2.me/theorems/00c29385-965c-460a-8a31-032aef01d98a
-- title:
--   PAdic Hodge: series Eval subst
-- statement:
--   The PAdic Hodge construction uses the series Eval subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L156-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L156-L168

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open PowerSeries
variable {B : Type*} [CommRing B] (I : Ideal B)
variable [Algebra ℚ B]
variable [IsAdicComplete I B]
variable {I}

theorem GroundTheory.PAdicHodge.seriesEval_subst {z : B} (hz : z ∈ I) {g : ℚ⟦X⟧} (hg : constantCoeff g = 0) {w : B}
    (hw : w ∈ I) (hgw : seriesEval I z hz g = w) (f : ℚ⟦X⟧) :
    seriesEval I w hw f = seriesEval I z hz (f.subst g) := by sorry
