-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnfoldFlag_flagMat_mulVec
-- name    : GlobalTheory.RootEx.UnfoldFlag.flagMat_mulVec
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:04.656996+00:00
-- url     : https://prove2.me/theorems/04302d80-ec74-49da-a48c-cf1e538e179c
-- title:
--   Unfold Flag: flag Mat mul Vec
-- statement:
--   The Unfold Flag construction uses the flag Mat mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsUnipotent.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsUnipotent.lean#L17-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsUnipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldFlag
variable {k : Type} [Field k] [ValuativeRel k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem GlobalTheory.RootEx.UnfoldFlag.flagMat_mulVec (y : Fin c → (n ⊕ Fin c → k)) (v : n ⊕ Fin c → k) :
    flagMat y *ᵥ v = inX k n c (fun r => v (Sum.inl r)) + ∑ i, v (Sum.inr i) • y i := by sorry
