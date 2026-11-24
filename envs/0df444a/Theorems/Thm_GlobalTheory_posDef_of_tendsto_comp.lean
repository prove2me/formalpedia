-- Prove2me | Theorems.Thm_GlobalTheory_posDef_of_tendsto_comp
-- name    : GlobalTheory.posDef_of_tendsto_comp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:13:52.246528+00:00
-- url     : https://prove2.me/theorems/d91b5f69-d25b-4e10-a6c4-398f90c8adf4
-- title:
--   Global Theory: pos Def of tendsto comp
-- statement:
--   The Global Theory construction uses the pos Def of tendsto comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L223-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L223-L240

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory

theorem GlobalTheory.posDef_of_tendsto_comp {X V : Type*} [AddCommGroup X] [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (φ : X →+ V) (hφ : Submodule.span ℝ (Set.range φ) = ⊤)
    (Q : QuadraticForm ℝ V) (h : Tendsto (fun x => Q (φ x)) cofinite atTop) : Q.PosDef := by sorry
