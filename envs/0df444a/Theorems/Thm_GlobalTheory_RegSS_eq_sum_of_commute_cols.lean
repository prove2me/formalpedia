-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_eq_sum_of_commute_cols
-- name    : GlobalTheory.RegSS.eq_sum_of_commute_cols
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T06:20:43.398655+00:00
-- url     : https://prove2.me/theorems/233695dc-25ff-5c35-8b8d-193d450a83b6
-- title:
--   Reg SS: eq sum of commute cols
-- statement:
--   The Reg SS construction uses the eq sum of commute cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RegularSemisimpleTensorCommutant.lean#L33-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RegularSemisimpleTensorCommutant.lean#L33-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RegularSemisimpleTensorCommutant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.RegSS.eq_sum_of_commute_cols {c : n → Matrix n n A} {v : n → A} (hB : IsUnit (colMat c v))
    (hc : ∀ i j, c i * c j = c j * c i) {N : Matrix n n A} (hN : ∀ j, N * c j = c j * N) :
    ∃ a : n → A, ∑ j, a j • c j = N := by sorry
