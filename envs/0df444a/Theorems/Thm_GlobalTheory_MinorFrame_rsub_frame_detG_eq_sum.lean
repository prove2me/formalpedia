-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_rsub_frame_detG_eq_sum
-- name    : GlobalTheory.MinorFrame.rsub_frame_detG_eq_sum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:14:52.072696+00:00
-- url     : https://prove2.me/theorems/8e765753-f30a-46c4-982c-130ee996c399
-- title:
--   Minor Frame: rsub frame det G eq sum
-- statement:
--   The Minor Frame construction uses the rsub frame det G eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CauchyBinetColumnFrameProdDetPowEqSum.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CauchyBinetColumnFrameProdDetPowEqSum.lean#L71-L74

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

theorem GlobalTheory.MinorFrame.rsub_frame_detG_eq_sum : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (x₀ : Var ι d a → ℂ),
    rsub (frameMat x₀).conjTranspose (detG a n) =
      ∑ T : Tup ι a d n, star (MvPolynomial.eval x₀ (prodMinors T)) • prodMinors T := by sorry
