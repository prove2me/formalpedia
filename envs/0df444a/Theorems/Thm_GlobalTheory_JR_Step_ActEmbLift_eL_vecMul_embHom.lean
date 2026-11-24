-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_ActEmbLift_eL_vecMul_embHom
-- name    : GlobalTheory.JR.Step.ActEmbLift.eL_vecMul_embHom
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:35:29.279816+00:00
-- url     : https://prove2.me/theorems/ff5857ac-d949-4b53-ae3f-bb77cea932b3
-- title:
--   Act Emb Lift: e L vec Mul emb Hom
-- statement:
--   The Act Emb Lift construction uses the e L vec Mul emb Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BorderedConjugationDiagOneLiftBlockMatrix.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BorderedConjugationDiagOneLiftBlockMatrix.lean#L28-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedConjugationDiagOneLiftBlockMatrix
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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step GlobalTheory.JR.Step.ActEmbLift

theorem GlobalTheory.JR.Step.ActEmbLift.eL_vecMul_embHom (k : Type) [CommRing k] (r : ℕ) (g : Matrix (Fin r) (Fin r) k) :
    eL r k ᵥ* embHom r k g = eL r k := by sorry
