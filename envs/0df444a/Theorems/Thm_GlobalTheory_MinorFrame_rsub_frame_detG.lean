-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_rsub_frame_detG
-- name    : GlobalTheory.MinorFrame.rsub_frame_detG
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:16:04.069179+00:00
-- url     : https://prove2.me/theorems/ec80a7cd-c396-48a9-be60-12cba9b84ea6
-- title:
--   Minor Frame: rsub frame det G
-- statement:
--   The Minor Frame construction uses the rsub frame det G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CauchyBinetColumnFrameProdDetPowEqSum.lean#L56-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CauchyBinetColumnFrameProdDetPowEqSum.lean#L56-L65

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
noncomputable section
open GlobalTheory GlobalTheory.MinorFrame
open scoped Matrix
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.MinorFrame.rsub_frame_detG {a d : ℕ} (n : ι → ℕ) (x₀ : Var ι d a → ℂ) :
    rsub (frameMat x₀).conjTranspose (detG a n) =
      ∑ T : Tup ι a d n, star (eval x₀ (prodMinors T)) • prodMinors T := by sorry
