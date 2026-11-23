-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_adj_add
-- name    : GlobalTheory.RegSS.adj_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:09.903439+00:00
-- url     : https://prove2.me/theorems/35a8e1fa-d55a-4533-ade4-c52c5f18e96b
-- title:
--   Reg SS: adj add
-- statement:
--   The Reg SS construction uses the adj add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L309-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L309-L311

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
open Matrix NumberField
open scoped TensorProduct
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.RegSS.adj_add (σ : A →+* A) (J a b : Matrix n n A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J (a + b) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J a + _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J b := by sorry
