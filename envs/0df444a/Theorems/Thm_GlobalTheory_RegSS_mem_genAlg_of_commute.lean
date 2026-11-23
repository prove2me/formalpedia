-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_mem_genAlg_of_commute
-- name    : GlobalTheory.RegSS.mem_genAlg_of_commute
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:33.396259+00:00
-- url     : https://prove2.me/theorems/b4c468fc-c5a2-4979-b98f-96ab8f0dbe5e
-- title:
--   Reg SS: mem gen Alg of commute
-- statement:
--   The Reg SS construction uses the mem gen Alg of commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L456-L474
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L456-L474

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

theorem GlobalTheory.RegSS.mem_genAlg_of_commute {M N : Matrix n n A} {v : n → A}
    (hv : Function.Bijective (fun l : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg M => (l : Matrix n n A) *ᵥ v))
    (h : N * M = M * N) : N ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg M := by sorry
