-- Prove2me | Theorems.Thm_GlobalTheory_JR_EtQuot_nontrivial_quot
-- name    : GlobalTheory.JR.EtQuot.nontrivial_quot
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:31:24.277045+00:00
-- url     : https://prove2.me/theorems/b7a984aa-3b08-4356-a19d-5fcc8466a4ad
-- title:
--   Et Quot: nontrivial quot
-- statement:
--   The Et Quot construction uses the nontrivial quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsEtaleInvolutiveAlgebraSplittingSmaller.lean#L155-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsEtaleInvolutiveAlgebraSplittingSmaller.lean#L155-L157

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEtaleInvolutiveAlgebraSplittingSmaller
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtQuot

theorem GlobalTheory.JR.EtQuot.nontrivial_quot {K : Type} [CommRing K] {e : K} (he : IsIdempotentElem e) (h1 : e ≠ 1) :
    Nontrivial (K ⧸ Ideal.span {e}) := by sorry
