-- Prove2me | Theorems.Thm_GlobalTheory_DiagBlock_kill_X
-- name    : GlobalTheory.DiagBlock.kill_X
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:47:30.961864+00:00
-- url     : https://prove2.me/theorems/76b8cf44-f297-45ad-acbf-7e0f5db2e7e9
-- title:
--   Diag Block: kill X
-- statement:
--   The Diag Block construction uses the kill X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L46-L48

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock
variable {R : Type} [CommRing R] {σ : Type}

theorem GlobalTheory.DiagBlock.kill_X (S : σ → Prop) [DecidablePred S] (x : σ) :
    kill (R := R) S (MvPolynomial.X x) = if S x then 0 else MvPolynomial.X x := by sorry
