-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_ActEmbLift_embHom_mul_full_mul
-- name    : GlobalTheory.JR.Step.ActEmbLift.embHom_mul_full_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:35:31.266071+00:00
-- url     : https://prove2.me/theorems/90952bd3-d2f1-47ef-81e0-2bea636796a7
-- title:
--   Act Emb Lift: emb Hom mul full mul
-- statement:
--   The Act Emb Lift construction uses the emb Hom mul full mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BorderedConjugationDiagOneLiftBlockMatrix.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BorderedConjugationDiagOneLiftBlockMatrix.lean#L9-L17

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

theorem GlobalTheory.JR.Step.ActEmbLift.embHom_mul_full_mul (k : Type) [CommRing k] (r : ℕ) (g h : Matrix (Fin r) (Fin r) k) (Z : Gl r k) :
    embHom r k g * full Z * embHom r k h = full (g * Z.1 * h, g *ᵥ Z.2.1, Z.2.2.1 ᵥ* h, Z.2.2.2) := by sorry
