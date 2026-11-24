-- Prove2me | Theorems.Thm_GlobalTheory_ColLie_colDer_X
-- name    : GlobalTheory.ColLie.colDer_X
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:19:10.478904+00:00
-- url     : https://prove2.me/theorems/08d181e7-eeec-4bff-8841-401af2b5d0ab
-- title:
--   Col Lie: col Der X
-- statement:
--   The Col Lie construction uses the col Der X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColDerApply.lean#L25-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColDerApply.lean#L25-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColDerApply
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
open GlobalTheory GlobalTheory.ColLie
open GlobalTheory.MinorFrame
variable {ι : Type} [DecidableEq ι]

theorem GlobalTheory.ColLie.colDer_X {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (v : Var ι d a) :
    colDer (d := d) τ S (X v) = if v.1 = τ then ∑ k, S k v.2.2 • (X (τ, v.2.1, k) : Pol ι d a) else 0 := by sorry
