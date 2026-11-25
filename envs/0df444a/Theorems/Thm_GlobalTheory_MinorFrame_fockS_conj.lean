-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_fockS_conj
-- name    : GlobalTheory.MinorFrame.fockS_conj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:22:39.881441+00:00
-- url     : https://prove2.me/theorems/f4e8cc53-1cbb-56fa-986b-b47e1f2ae307
-- title:
--   Minor Frame: fock S conj
-- statement:
--   The Minor Frame construction uses the fock S conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdMinorsMemInv.lean#L97-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdMinorsMemInv.lean#L97-L103

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.MinorFrame
open Classical
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.MinorFrame.fockS_conj {σ : Type} (f g : MvPolynomial σ ℂ) :
    Formalism.L2.DIV.fockS f g = starRingEnd ℂ (Formalism.L2.DIV.fockS g f) := by sorry
