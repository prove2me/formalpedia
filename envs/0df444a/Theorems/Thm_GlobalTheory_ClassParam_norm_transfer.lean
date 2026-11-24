-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_norm_transfer
-- name    : GlobalTheory.ClassParam.norm_transfer
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:13:34.079134+00:00
-- url     : https://prove2.me/theorems/d7b644da-9835-4df3-b1be-3744da1c531c
-- title:
--   Class Param: norm transfer
-- statement:
--   The Class Param construction uses the norm transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L143-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L143-L149

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
variable {R S A B : Type} [CommRing R] [CommRing S] [CommRing A] [CommRing B] [Algebra R S]
  [Algebra A B] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.ClassParam.norm_transfer (f : R →+* A) (ψ : S →+* B)
    (h : ∀ a, ψ (algebraMap R S a) = algebraMap A B (f a)) (b : Module.Basis ι R S)
    (b' : Module.Basis ι A B) (hb : ∀ i, ψ (b i) = b' i) (x : S) :
    Algebra.norm A (ψ x) = f (Algebra.norm R x) := by sorry
