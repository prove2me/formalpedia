-- Prove2me | Theorems.Thm_GlobalTheory_LineCos_FsLaw_measurable_hform
-- name    : GlobalTheory.LineCos.FsLaw.measurable_hform
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:58.419774+00:00
-- url     : https://prove2.me/theorems/1f79d63d-6044-43d9-9b8e-d02859b045e2
-- title:
--   Fs Law: measurable hform
-- statement:
--   The Fs Law construction uses the measurable hform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CosineSquarePushforwardUniform.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CosineSquarePushforwardUniform.lean#L47-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StereographicMeasureChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusChangeOfVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder ENNReal
noncomputable section
open GlobalTheory GlobalTheory.LineCos GlobalTheory.LineCos.FsLaw
open GlobalTheory.LineCos

theorem GlobalTheory.LineCos.FsLaw.measurable_hform (G : Matrix (Fin 2) (Fin 2) ℂ) {a b : ℂ → Fin 2 → ℂ} (ha : ∀ i, Measurable fun x => a x i)
    (hb : ∀ i, Measurable fun x => b x i) : Measurable fun x => hform G (a x) (b x) := by sorry
