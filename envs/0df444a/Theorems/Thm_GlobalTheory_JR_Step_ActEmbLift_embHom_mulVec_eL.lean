-- Prove2me | Theorems.Thm_GlobalTheory_JR_Step_ActEmbLift_embHom_mulVec_eL
-- name    : GlobalTheory.JR.Step.ActEmbLift.embHom_mulVec_eL
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:35:51.316822+00:00
-- url     : https://prove2.me/theorems/b7d033e0-8f80-43d2-8da8-9ed50176d699
-- title:
--   Act Emb Lift: emb Hom mul Vec e L
-- statement:
--   The Act Emb Lift construction uses the emb Hom mul Vec e L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BorderedConjugationDiagOneLiftBlockMatrix.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BorderedConjugationDiagOneLiftBlockMatrix.lean#L19-L26

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

theorem GlobalTheory.JR.Step.ActEmbLift.embHom_mulVec_eL (k : Type) [CommRing k] (r : ℕ) (g : Matrix (Fin r) (Fin r) k) :
    embHom r k g *ᵥ eL r k = eL r k := by sorry
