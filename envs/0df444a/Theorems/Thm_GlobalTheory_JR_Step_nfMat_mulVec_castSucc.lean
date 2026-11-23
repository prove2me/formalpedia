-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_nfMat_mulVec_castSucc
-- name    : GlobalTheory.JR.Step.nfMat_mulVec_castSucc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:46.105799+00:00
-- url     : https://prove2.me/theorems/473e8023-2456-44ad-a078-ba75660b1829
-- title:
--   Step: nf Mat mul Vec cast Succ
-- statement:
--   The Step construction uses the nf Mat mul Vec cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGlConjugateLastBasisNormalFormOfNeZero.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGlConjugateLastBasisNormalFormOfNeZero.lean#L16-L24

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

theorem GlobalTheory.JR.Step.nfMat_mulVec_castSucc {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) (v : Fin (r + 1) → k)
    (i : Fin r) : (nfMat c *ᵥ v) (Fin.castSucc i) = v i.succ := by sorry
