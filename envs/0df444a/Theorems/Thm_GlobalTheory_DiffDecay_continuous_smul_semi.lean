-- Prove2me | Theorems.Thm_GlobalTheory_DiffDecay_continuous_smul_semi
-- name    : GlobalTheory.DiffDecay.continuous_smul_semi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:23.120671+00:00
-- url     : https://prove2.me/theorems/ddf2965c-9fc8-4f05-8cee-4011675b3cae
-- title:
--   Diff Decay: continuous smul semi
-- statement:
--   The Diff Decay construction uses the continuous smul semi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousSmulSemi.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousSmulSemi.lean#L53-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousSmulSemi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic
noncomputable section
open GlobalTheory GlobalTheory.DiffDecay
variable {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] {W : Type} [SeminormedAddCommGroup W]

theorem GlobalTheory.DiffDecay.continuous_smul_semi (c : ℝ) (q : Seminorm ℂ E) (hq : Continuous q) :
    ∃ q' : Seminorm ℂ E, Continuous q' ∧ ∀ f, q' f = |c| * q f := by sorry
