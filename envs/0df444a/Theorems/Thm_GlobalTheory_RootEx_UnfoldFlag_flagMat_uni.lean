-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnfoldFlag_flagMat_uni
-- name    : GlobalTheory.RootEx.UnfoldFlag.flagMat_uni
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:06.542135+00:00
-- url     : https://prove2.me/theorems/8c7167f3-eab1-40bb-b71d-33d699b96537
-- title:
--   Unfold Flag: flag Mat uni
-- statement:
--   The Unfold Flag construction uses the flag Mat uni property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsUnipotent.lean#L29-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsUnipotent.lean#L29-L47

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

theorem GlobalTheory.RootEx.UnfoldFlag.flagMat_uni {y : Fin c → (n ⊕ Fin c → k)} (hY : ∀ i, y i ∈ Yle k n c (i.val + 1))
    (h1 : ∀ i, y i (Sum.inr i) = 1) (h0 : ∀ i : Fin c, i.val = 0 → ∀ r, y i (Sum.inl r) = 0) :
    Radical.Uni (lev 1) (flagMat y) := by sorry
