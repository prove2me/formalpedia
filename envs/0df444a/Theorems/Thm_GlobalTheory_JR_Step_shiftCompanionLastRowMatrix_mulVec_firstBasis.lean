-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_shiftCompanionLastRowMatrix_mulVec_firstBasis
-- name    : GlobalTheory.JR.Step.shiftCompanionLastRowMatrix_mulVec_firstBasis
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:36:47.993129+00:00
-- url     : https://prove2.me/theorems/a9708e1f-2c2c-415e-950f-a7497c3b2fb0
-- title:
--   Step: shift Companion Last Row Matrix mul Vec first Basis
-- statement:
--   The Step construction uses the shift Companion Last Row Matrix mul Vec first Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGlConjugateLastBasisNormalFormOfNeZero.lean#L54-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGlConjugateLastBasisNormalFormOfNeZero.lean#L54-L61

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

theorem GlobalTheory.JR.Step.shiftCompanionLastRowMatrix_mulVec_firstBasis {r : ℕ} {k : Type} [CommRing k] (c : Fin (r + 1) → k) :
    nfMat c *ᵥ (fun i : Fin (r + 1) => if (i : ℕ) = 0 then (1 : k) else 0) = c 0 • eL r k := by sorry
