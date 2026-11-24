-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_nfMat_mulVec_last
-- name    : GlobalTheory.JR.Step.nfMat_mulVec_last
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:37:51.927355+00:00
-- url     : https://prove2.me/theorems/f400605f-854e-45e4-bee3-1b594a596ae3
-- title:
--   Step: nf Mat mul Vec last
-- statement:
--   The Step construction uses the nf Mat mul Vec last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGlConjugateLastBasisNormalFormOfNeZero.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGlConjugateLastBasisNormalFormOfNeZero.lean#L26-L28

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGlConjugateLastBasisNormalFormOfNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step

theorem GlobalTheory.JR.Step.nfMat_mulVec_last {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) (v : Fin (r + 1) → k) :
    (nfMat c *ᵥ v) (Fin.last r) = c ⬝ᵥ v := by sorry
