-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_HidaSetting_trace_star
-- name    : GlobalTheory.ClassParam.HidaSetting.trace_star
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:32.968771+00:00
-- url     : https://prove2.me/theorems/2a8358ca-c5b8-4ec6-bbcf-493ae6409fcd
-- title:
--   Hida Setting: trace star
-- statement:
--   The Hida Setting construction uses the trace star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L243-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L243-L250

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}
variable {σ : A →+* A} {τ : B →+* B} {α : B} {b : Module.Basis (Fin r) A B}
  {J : Matrix (Fin r) (Fin r) A}

theorem GlobalTheory.ClassParam.HidaSetting.trace_star (S : HidaSetting σ τ α b) (z : B) :
    Algebra.trace A B (τ z) = σ (Algebra.trace A B z) := by sorry
