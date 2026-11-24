-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_rsub_frame_X
-- name    : GlobalTheory.MinorFrame.rsub_frame_X
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:16:21.421972+00:00
-- url     : https://prove2.me/theorems/48bc1924-94bc-476e-9c94-192289996bee
-- title:
--   Minor Frame: rsub frame X
-- statement:
--   The Minor Frame construction uses the rsub frame X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CauchyBinetColumnFrameProdDetPowEqSum.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CauchyBinetColumnFrameProdDetPowEqSum.lean#L19-L31

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

theorem GlobalTheory.MinorFrame.rsub_frame_X {a d : ℕ} (x₀ : Var ι d a → ℂ) (τ : ι) (i j : Fin a) :
    rsub (frameMat x₀)ᴴ (X (τ, i, j)) = ∑ r : Fin d, C (star (x₀ (τ, r, i))) * (X (τ, r, j) : Pol ι d a) := by sorry
