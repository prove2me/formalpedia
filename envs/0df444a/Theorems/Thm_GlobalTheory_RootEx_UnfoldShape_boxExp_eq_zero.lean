-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_boxExp_eq_zero
-- name    : GlobalTheory.RootEx.UnfoldShape.boxExp_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:15.147977+00:00
-- url     : https://prove2.me/theorems/92c248ff-ac39-4cc0-981e-b9495e59f2d1
-- title:
--   Unfold Shape: box Exp eq zero
-- statement:
--   The Unfold Shape construction uses the box Exp eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/VolFreePerLatStdLat.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/VolFreePerLatStdLat.lean#L15-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_VolFreePerLatStdLat
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
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldShape

theorem GlobalTheory.RootEx.UnfoldShape.boxExp_eq_zero {n n' : Type} {c : ℕ} (rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))
    (h : ¬ Free 1 rs) : boxExp rs = 0 := by sorry
