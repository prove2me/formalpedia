-- Prove2me | Theorems.Thm_GlobalTheory_lagrRankOne_adm
-- name    : GlobalTheory.lagrRankOne_adm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:02:31.855424+00:00
-- url     : https://prove2.me/theorems/afa87159-2858-4567-a8f0-f6b94821a6dc
-- title:
--   Global Theory: lagr Rank One adm
-- statement:
--   The Global Theory construction uses the lagr Rank One adm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAdmissibleLagrangianTransverseField.lean#L27-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAdmissibleLagrangianTransverseField.lean#L27-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdmissibleLagrangianTransverseField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem GlobalTheory.lagrRankOne_adm {k : Type} [Field k] (c : k →+* k) {n : ℕ}
    (S : Matrix (Fin n) (Fin n) k) (hS : Sᵀ = -S.map c) (j : Fin n) :
    (lagrRankOne S j)ᵀ * S + S * (lagrRankOne S j).map c = 0 := by sorry
