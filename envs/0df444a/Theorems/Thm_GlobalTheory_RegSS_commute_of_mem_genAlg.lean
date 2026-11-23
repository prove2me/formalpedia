-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_commute_of_mem_genAlg
-- name    : GlobalTheory.RegSS.commute_of_mem_genAlg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:38.598593+00:00
-- url     : https://prove2.me/theorems/1d5d5222-c418-4ac1-9a37-6ca3348907ad
-- title:
--   Reg SS: commute of mem gen Alg
-- statement:
--   The Reg SS construction uses the commute of mem gen Alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L447-L450
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L447-L450

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

theorem GlobalTheory.RegSS.commute_of_mem_genAlg {M N l : Matrix n n A} (h : N * M = M * N)
    (hl : l ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg M) : N * l = l * N := by sorry
