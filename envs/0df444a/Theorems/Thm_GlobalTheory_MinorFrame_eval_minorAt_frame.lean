-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_eval_minorAt_frame
-- name    : GlobalTheory.MinorFrame.eval_minorAt_frame
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:16:04.079264+00:00
-- url     : https://prove2.me/theorems/51eed1e9-57e8-42df-8324-ba06be2161c4
-- title:
--   Minor Frame: eval minor At frame
-- statement:
--   The Minor Frame construction uses the eval minor At frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CauchyBinetColumnFrameProdDetPowEqSum.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CauchyBinetColumnFrameProdDetPowEqSum.lean#L11-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumNormRowSubProdMinors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CauchyBinetColumnFrameProdDetPowEqSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.MinorFrame
open scoped Matrix
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.MinorFrame.eval_minorAt_frame {a d : ℕ} (x₀ : Var ι d a → ℂ) (τ : ι) (s : Fin a → Fin d) :
    eval x₀ (minorAt τ s) = ((Matrix.of fun (r : Fin d) (i : Fin a) => x₀ (τ, r, i)).submatrix s id).det := by sorry
