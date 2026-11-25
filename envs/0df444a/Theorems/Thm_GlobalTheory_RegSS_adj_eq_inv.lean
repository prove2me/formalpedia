-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_adj_eq_inv
-- name    : GlobalTheory.RegSS.adj_eq_inv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:33:11.997628+00:00
-- url     : https://prove2.me/theorems/2c11f658-b755-48b4-839b-45b215eeb618
-- title:
--   Reg SS: adj eq inv
-- statement:
--   The Reg SS construction uses the adj eq inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L438-L442
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L438-L442

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

theorem GlobalTheory.RegSS.adj_eq_inv (σ : A →+* A) {J : Matrix n n A}
    (hJ : IsUnit J.det) {g : GL n A} (hg : g ∈ _root_.Formalism.UG.UJ σ J) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J (g : Matrix n n A) = ((g⁻¹ : GL n A) : Matrix n n A) := by sorry
