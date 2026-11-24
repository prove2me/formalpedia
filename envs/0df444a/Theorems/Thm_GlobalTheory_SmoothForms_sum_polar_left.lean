-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_sum_polar_left
-- name    : GlobalTheory.SmoothForms.sum_polar_left
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:19:09.414307+00:00
-- url     : https://prove2.me/theorems/f551463b-9ee6-4b39-93dd-bbff0f789910
-- title:
--   Smooth Forms: sum polar left
-- statement:
--   The Smooth Forms construction uses the sum polar left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/CommutatorGlGeneratorTensorWordMapMatrixUnits.lean#L26-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/CommutatorGlGeneratorTensorWordMapMatrixUnits.lean#L26-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutatorGlGeneratorTensorWordMapMatrixUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms

theorem GlobalTheory.SmoothForms.sum_polar_left {A : Type} [AddCommGroup A] [Module ℂ A] {n d : ℕ} (a b : Fin n) (I : Fin d → Fin n)
    (g : (Fin d → Fin n) → A) :
    ∑ J, polar n d a b J I • g J = ∑ p, if b = I p then g (Function.update I p a) else 0 := by sorry
